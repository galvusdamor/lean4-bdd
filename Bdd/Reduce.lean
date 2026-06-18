import Bdd.Collect
import Bdd.Trim
import Bdd.Canonical

open Pointer
open Bdd

private def OBdd.discover_helper : List (Fin m) → Vector (Node n m ) m → Vector (List (Fin m)) n → Vector (List (Fin m)) n
  | [], _, I => I
  | head :: tail, v, I => discover_helper tail v (I.set v[head].var (head :: I[v[head].var]))

private lemma OBdd.discover_helper_retains_found (O : OBdd n m) {I : Vector (List (Fin m)) n} {i : Fin n}: j ∈ I[i] → j ∈ (discover_helper l v I)[i] := by
  intro h
  cases l with
  | nil => assumption
  | cons head tail =>
    simp [discover_helper]
    apply discover_helper_retains_found O
    cases decEq v[head.1].var i with
    | isFalse hf =>
      simp only [Fin.getElem_fin]
      rw [Vector.getElem_set_ne _ _ (by simp_all [Fin.val_ne_of_ne hf])]
      assumption
    | isTrue  ht =>
      subst ht
      simp only [Fin.getElem_fin]
      rw [Vector.getElem_set_self]
      right
      assumption

private lemma OBdd.discover_helper_spec (O : OBdd n m) {I : Vector (List (Fin m)) n} :
    j ∈ l → j ∈ (discover_helper l v I).get v[j].var := by
  intro h
  cases h with
  | head as =>
    simp [discover_helper]
    apply discover_helper_retains_found O
    simp only [Fin.getElem_fin]
    rw [Vector.getElem_set_self]
    left
  | tail b ih =>
    simp [discover_helper]
    apply discover_helper_spec O ih

/-- Return a vector whose `v`th entry is a list of node indices with variable index `v`.

This is a subroutine of `reduce`.  -/
def OBdd.discover (O : OBdd n m) : Vector (List (Fin m)) n := discover_helper (Collect.collect O) O.1.heap (Vector.replicate n [])

/-- `discover` is correct. -/
theorem OBdd.discover_spec {O : OBdd n m} {j : Fin m} :
    (Reachable O.1.heap O.1.root (node j)) → j ∈ (discover O).get O.1.heap[j].var :=
  (discover_helper_spec O) ∘ Collect.collect_spec

/-
Membership in a bucket of `discover_helper`: `j` is in bucket `k` iff it was
already there, or it is in the worklist `l` and has variable index `k`.
-/
private lemma OBdd.discover_helper_get_iff {l : List (Fin m)} {v : Vector (Node n m) m}
    {I : Vector (List (Fin m)) n} {k : Fin n} {j : Fin m} :
    j ∈ (discover_helper l v I)[k] ↔ j ∈ I[k] ∨ (j ∈ l ∧ v[j].var = k) := by
  induction' l with head tail ih generalizing I
  · simp [discover_helper]
  · convert ih using 1
    grind +revert

/-
Characterisation of the buckets produced by `discover`: bucket `k` contains
exactly the reachable nodes with variable index `k`.
-/
theorem OBdd.mem_discover_iff {O : OBdd n m} {k : Fin n} {j : Fin m} :
    j ∈ (discover O)[k] ↔
      (Reachable O.1.heap O.1.root (node j) ∧ O.1.heap[j].var = k) := by
  convert ( OBdd.discover_helper_get_iff ( k := k ) ( l := Collect.collect O ) ( v := O.1.heap ) ( I := Vector.replicate n [] ) ) using 1
  simp +decide [ Collect.mem_collect_iff_reachable ]

/-
`discover_helper` keeps every bucket duplicate-free, provided the worklist is
duplicate-free and disjoint from the existing buckets.
-/
private lemma OBdd.discover_helper_nodup {l : List (Fin m)} {v : Vector (Node n m) m}
    {I : Vector (List (Fin m)) n} (hl : l.Nodup) (hI : ∀ k : Fin n, (I[k]).Nodup)
    (hdisj : ∀ (k : Fin n) (j : Fin m), j ∈ I[k] → j ∉ l) :
    ∀ k : Fin n, ((discover_helper l v I)[k]).Nodup := by
  induction' l with head tail ih generalizing I <;> simp_all +decide [ OBdd.discover_helper ]
  grind

/-- Each bucket of `discover` is duplicate-free (it is selected from the
duplicate-free `collect`). -/
theorem OBdd.discover_nodup {O : OBdd n m} {k : Fin n} : ((discover O)[k]).Nodup := by
  refine discover_helper_nodup Collect.collect_nodup (fun k => ?_) (fun k j hj => ?_) k
  · simp [Vector.getElem_replicate]
  · simp [Vector.getElem_replicate] at hj

namespace Reduce
private structure State (n) (m) where
  out : Vector (Node n m) m
  ids : Vector (Pointer m) m
  nid : Fin m

private def initial {n m : Nat} : State n.succ m.succ :=
  ⟨ (Vector.replicate m.succ {var := 0, low := terminal false, high := terminal true}),
    (Vector.replicate m.succ (terminal false)),
    Fin.last m
  ⟩

private def get_out : StateM (State n m) (Vector (Node n m) m) := get >>= fun s ↦ pure s.out

private def get_id : Pointer m → StateM (State n m) (Pointer m)
  | terminal b => pure (terminal b)
  | node j => get >>= fun s ↦ pure (s.ids[j])

private def set_id : Fin m → Pointer m → StateM (State n m) Unit :=
  fun j p ↦ get >>= fun s ↦ set (⟨s.out, s.ids.set j p, s.nid⟩ : State n m)

private def set_id_to_nid : Fin m → StateM (State n m) Unit :=
  fun j ↦ get >>= fun s ↦ set_id j (node s.nid)

private def set_out {n m : Nat} : Node n.succ m.succ → StateM (State n.succ m.succ) Unit :=
  fun N ↦ get >>= fun s ↦
    have : (s.nid.1 + 1) % m.succ < m.succ := Nat.mod_lt _ (Nat.succ_pos _)
    set (⟨s.out.set ((s.nid.1 + 1) % m.succ) N, s.ids, s.nid + 1⟩ : State n.succ m.succ)

private def populate_queue (v : Vector (Node n m) m) (acc : List ((Pointer m × Pointer m) × Fin m)) : List (Fin m) → StateM (State n m) (List ((Pointer m × Pointer m) × Fin m))
  | [] => pure acc
  | j :: tail => do
    let lid ← get_id v[j].low
    let hid ← get_id v[j].high
    if decide (lid = hid)
    then
      -- `node j` is redundant in the original BDD.
      --  Reduce it by mapping it to its child `lid` in the output BDD.
      set_id j lid
      populate_queue v acc tail
    else populate_queue v (⟨⟨lid, hid⟩, j⟩ :: acc) tail

private def process_record {n m : Nat} (v : Vector (Node n.succ m.succ) m.succ) (curkey : Pointer m.succ × Pointer m.succ) : (Pointer m.succ × Pointer m.succ) × Fin m.succ → StateM (State n.succ m.succ) (Pointer m.succ × Pointer m.succ) := fun ⟨key, j⟩ ↦ do
  if key = curkey
  then
    -- isomorphism in original BDD, reduce.
    set_id_to_nid j
    pure curkey
  else
    let lid ← get_id v[j].low
    let hid ← get_id v[j].high
    set_out ⟨v[j].var, lid, hid⟩
    set_id_to_nid j
    pure key

private def process_queue {n m : Nat} (v : Vector (Node n.succ m.succ) m.succ) (curkey : Pointer m.succ × Pointer m.succ) :
  List ((Pointer m.succ × Pointer m.succ) × Fin m.succ) → StateM (State n.succ m.succ) Unit
  | [] => pure ()
  | head :: tail => do
    let newkey ← process_record v curkey head
    process_queue v newkey tail

/-- A *total* lexicographic order on dedup keys `((low, high), j)`.

The `Pointer` order `Pointer.le` is total, but the `≤` induced on a product is
the *product* (partial) order, under which `List.mergeSort` need not place equal
`(low, high)` keys contiguously.  Since `process_queue` only merges *adjacent*
equal keys, sorting with the product order can leave isomorphic nodes unmerged
(producing a non-reduced result).  Sorting with this genuinely total order groups
all equal keys together so that isomorphic nodes are reliably merged. -/
private def keyLe {m : Nat} (a b : (Pointer m × Pointer m) × Fin m) : Bool :=
  if a.1.1 = b.1.1 then
    if a.1.2 = b.1.2 then decide (a.2 ≤ b.2) else decide (a.1.2 ≤ b.1.2)
  else decide (a.1.1 ≤ b.1.1)

private def step {n m : Nat} (v : Vector (Node n.succ m.succ) m.succ) (vlist : Vector (List (Fin m.succ)) n.succ) (i : Fin n.succ) : StateM (State n.succ m.succ) Unit := do
  let Q ← populate_queue v [] vlist[i]
  process_queue v ⟨node 0, node 0⟩ (List.mergeSort Q keyLe)

private def loop {n m : Nat} (v : Vector (Node n.succ m.succ) m.succ) (r : Fin m.succ) (vlist : Vector (List (Fin m.succ)) n.succ) (i : Fin n.succ) : StateM (State n.succ m.succ) (Bdd n.succ m.succ) := do
  step v vlist i
  match h : i.1 - v[r].var.1 with
  | Nat.zero =>
    let out ← get_out
    let rid ← get_id (node r)
    pure {heap := out, root := rid}
  | Nat.succ j =>
    loop v r vlist ⟨(j + v[r].var.1), by omega⟩
termination_by i.1 - v[r].var.1
decreasing_by simp_all

/-- Run the imperative reduction loop, returning the resulting `Bdd` together
with the final write counter `nid` (used to trim the result to its used slots).
A terminal root is already reduced and is returned unchanged. -/
private def reduce {n m : Nat} (O : OBdd n.succ m.succ) : Bdd n.succ m.succ × Fin m.succ :=
  match O.1.root with
  | terminal _ => ⟨O.1, 0⟩
  | node r =>
    let ⟨B, S⟩ := (StateT.run (loop O.1.heap r (OBdd.discover O) ⟨n, Nat.lt_add_one n⟩) initial)
    ⟨B, S.nid⟩

/-! ### Run-behaviour of the state primitives -/

@[simp] lemma get_out_run (s : State n m) : (get_out).run s = (s.out, s) := rfl

@[simp] lemma get_id_terminal_run (b : Bool) (s : State n m) :
    (get_id (terminal b)).run s = (terminal b, s) := rfl

@[simp] lemma get_id_node_run (j : Fin m) (s : State n m) :
    (get_id (node j)).run s = (s.ids[j], s) := rfl

@[simp] lemma set_id_run (j : Fin m) (p : Pointer m) (s : State n m) :
    (set_id j p).run s = ((), ⟨s.out, s.ids.set j p, s.nid⟩) := rfl

@[simp] lemma set_id_to_nid_run (j : Fin m) (s : State n m) :
    (set_id_to_nid j).run s = ((), ⟨s.out, s.ids.set j (node s.nid), s.nid⟩) := rfl

@[simp] lemma set_out_run {n m : Nat} (N : Node n.succ m.succ) (s : State n.succ m.succ) :
    (set_out N).run s =
      ((), ⟨s.out.set ((s.nid.1 + 1) % m.succ) N (Nat.mod_lt _ (Nat.succ_pos _)), s.ids, s.nid + 1⟩) := rfl

/-! ### Effect of the queue routines on the state components -/

/-
`populate_queue` leaves `out` unchanged.
-/
lemma populate_queue_out {n m : Nat} (v : Vector (Node n m) m)
    (acc : List ((Pointer m × Pointer m) × Fin m)) (l : List (Fin m)) (s : State n m) :
    ((populate_queue v acc l).run s).2.out = s.out := by
  induction l generalizing acc s with
  | nil => rfl
  | cons k l ih =>
    rw [populate_queue]
    cases hl : v[k].low <;> cases hh : v[k].high <;>
      simp [get_id, StateT.run_bind, StateT.run_get] <;>
      split <;> exact ih _ _

/-
`populate_queue` leaves `nid` unchanged.
-/
lemma populate_queue_nid {n m : Nat} (v : Vector (Node n m) m)
    (acc : List ((Pointer m × Pointer m) × Fin m)) (l : List (Fin m)) (s : State n m) :
    ((populate_queue v acc l).run s).2.nid = s.nid := by
  induction l generalizing acc s with
  | nil => rfl
  | cons k l ih =>
    rw [populate_queue]
    cases hl : v[k].low <;> cases hh : v[k].high <;>
      simp [get_id, StateT.run_bind, StateT.run_get] <;>
      split <;> exact ih _ _

/-- Resolve a pointer through the current `ids` map (the pure value computed by
`get_id`). -/
private def resolveId (s : State n m) : Pointer m → Pointer m
  | terminal b => terminal b
  | node j => s.ids[j]

@[simp] lemma get_id_run' (p : Pointer m) (s : State n m) :
    (get_id p).run s = (resolveId s p, s) := by cases p <;> rfl

/-- `resolveId` only reads `ids`, so setting `ids` at an index `j` not named by
`ptr` leaves `resolveId ptr` unchanged. -/
private lemma resolveId_set_ids_ne {n m : Nat} (s : State n m) (j : Fin m) (p : Pointer m)
    (ptr : Pointer m) (h : ∀ k, ptr = node k → k ≠ j) :
    resolveId ⟨s.out, s.ids.set j p, s.nid⟩ ptr = resolveId s ptr := by
  cases ptr with
  | terminal b => rfl
  | node k =>
    have hjk : (j : Nat) ≠ (k : Nat) :=
      fun hh => (h k rfl) (Fin.ext hh.symm)
    simp only [resolveId]
    exact Vector.getElem_set_ne j.2 k.2 hjk

/-- `resolveId` only reads the `ids` component, so it is unaffected by the `out`
and `nid` components of the state. -/
private lemma resolveId_ids_irrel {n m : Nat} (out out' : Vector (Node n m) m)
    (ids : Vector (Pointer m) m) (nid nid' : Fin m) (ptr : Pointer m) :
    resolveId ⟨out, ids, nid⟩ ptr = resolveId ⟨out', ids, nid'⟩ ptr := by
  cases ptr <;> rfl

/-- One-step unfolding of `populate_queue` on a cons, expressed in terms of the
pure `resolveId`.  Both `get_id`s leave the state unchanged, so the whole step is
either a single `ids` write (redundant case) or a pure push onto `acc`. -/
lemma populate_queue_cons_run {n m : Nat} (v : Vector (Node n m) m)
    (acc : List ((Pointer m × Pointer m) × Fin m)) (j : Fin m) (tail : List (Fin m))
    (s : State n m) :
    (populate_queue v acc (j :: tail)).run s =
      (if resolveId s v[j].low = resolveId s v[j].high
       then (populate_queue v acc tail).run
              ⟨s.out, s.ids.set j (resolveId s v[j].low), s.nid⟩
       else (populate_queue v
              ((⟨resolveId s v[j].low, resolveId s v[j].high⟩, j) :: acc) tail).run s) := by
  conv_lhs => unfold populate_queue
  simp only [StateT.run_bind, get_id_run', decide_eq_true_eq]
  show StateT.run (if resolveId s v[j].low = resolveId s v[j].high then
          (set_id j (resolveId s v[j].low) >>= fun _ => populate_queue v acc tail)
        else populate_queue v
          ((⟨resolveId s v[j].low, resolveId s v[j].high⟩, j) :: acc) tail) s = _
  split
  · rw [StateT.run_bind, set_id_run]; rfl
  · rfl

/-
`populate_queue` leaves `ids[k]` unchanged for indices `k` that are not in the
processed list `l`.
-/
lemma populate_queue_ids_ne {n m : Nat} (v : Vector (Node n m) m)
    (acc : List ((Pointer m × Pointer m) × Fin m)) (l : List (Fin m)) (s : State n m)
    (k : Fin m) (hk : k ∉ l) :
    ((populate_queue v acc l).run s).2.ids[k] = s.ids[k] := by
  induction l generalizing acc s with
  | nil => rfl
  | cons j tail ih =>
    rw [populate_queue_cons_run]
    simp only [List.mem_cons, not_or] at hk
    split
    · rw [ih _ _ hk.2]
      exact Vector.getElem_set_ne j.2 k.2 (Fin.val_ne_of_ne (Ne.symm hk.1))
    · exact ih _ _ hk.2

/-- `populate_queue` does not change how a pointer resolves, provided that pointer
does not point at a node in the processed list `l`. -/
lemma populate_queue_resolveId {n m : Nat} (v : Vector (Node n m) m)
    (acc : List ((Pointer m × Pointer m) × Fin m)) (l : List (Fin m)) (s : State n m)
    (p : Pointer m) (hp : ∀ j', p = node j' → j' ∉ l) :
    resolveId ((populate_queue v acc l).run s).2 p = resolveId s p := by
  cases p with
  | terminal _ => rfl
  | node j' => exact populate_queue_ids_ne v acc l s j' (hp j' rfl)

/-
Effect of `populate_queue` on `ids` at a *redundant* index `k` of `l`: it is
mapped to its (shared) resolved child.
-/
lemma populate_queue_ids_redundant {n m : Nat} (v : Vector (Node n m) m)
    (acc : List ((Pointer m × Pointer m) × Fin m)) (l : List (Fin m)) (s : State n m)
    (k : Fin m) (hk : k ∈ l) (hnd : l.Nodup)
    (hred : resolveId s v[k].low = resolveId s v[k].high)
    (hstable : ∀ j ∈ l, (∀ j', v[j].low = node j' → j' ∉ l) ∧ (∀ j', v[j].high = node j' → j' ∉ l)) :
    ((populate_queue v acc l).run s).2.ids[k] = resolveId s v[k].low := by
  induction' l with j l ih generalizing acc s k
  · contradiction
  · by_cases hkj : k = j
    · simp +decide [ hkj, populate_queue_cons_run ]
      split_ifs
      · convert populate_queue_ids_ne v acc l _ j _ using 1
        · simp +decide
        · grind
      · grind
    · rw [ populate_queue_cons_run ]
      split_ifs
      · convert ih acc _ k ( List.mem_of_ne_of_mem hkj hk ) ( List.Nodup.of_cons hnd ) _ _ using 1
        · convert populate_queue_resolveId v acc l s v[k].low _ |> Eq.symm using 1
          · convert populate_queue_resolveId v acc l s v[k].low _ |> Eq.symm using 1
            · convert populate_queue_resolveId v acc ( j :: l ) s v[k].low _ using 1
              · rw [ populate_queue_cons_run ]
                grind +suggestions
              · exact hstable k hk |>.1
            · grind
          · grind
        · convert hred using 1
          · convert populate_queue_resolveId v acc ( j :: l ) s v[k].low _ using 1
            · rw [ populate_queue_cons_run ]
              grind +suggestions
            · exact hstable k hk |>.1
          · convert populate_queue_resolveId v acc ( j :: l ) s ( v[k].high ) _ using 1
            · rw [ populate_queue_cons_run ]
              grind +suggestions
            · exact hstable k hk |>.2
        · grind
      · grind

/-
Effect of `populate_queue` on `ids` at a *non-redundant* index `k` of `l`: it
is left untouched.
-/
lemma populate_queue_ids_nonredundant {n m : Nat} (v : Vector (Node n m) m)
    (acc : List ((Pointer m × Pointer m) × Fin m)) (l : List (Fin m)) (s : State n m)
    (k : Fin m) (hk : k ∈ l) (hnd : l.Nodup)
    (hnred : resolveId s v[k].low ≠ resolveId s v[k].high)
    (hstable : ∀ j ∈ l, (∀ j', v[j].low = node j' → j' ∉ l) ∧ (∀ j', v[j].high = node j' → j' ∉ l)) :
    ((populate_queue v acc l).run s).2.ids[k] = s.ids[k] := by
  induction' l with j l ih generalizing acc s k
  · contradiction
  · by_cases hkj : k = j
    · subst hkj
      rw [populate_queue_cons_run, if_neg hnred]
      exact populate_queue_ids_ne v _ l s k (List.nodup_cons.mp hnd).1
    · rw [ populate_queue_cons_run ]
      split_ifs
      · convert ih acc _ k ( List.mem_of_ne_of_mem hkj hk ) ( List.Nodup.of_cons hnd ) _ _ using 1
        · grind
        · convert hnred using 1
          · convert populate_queue_resolveId v acc ( j :: l ) s v[k].low _ using 1
            · rw [ populate_queue_cons_run ]
              grind +suggestions
            · exact hstable k hk |>.1
          · convert populate_queue_resolveId v acc ( j :: l ) s v[k].high _ using 1
            · rw [ populate_queue_cons_run ]
              grind +suggestions
            · exact hstable k hk |>.2
        · grind
      · grind

/-
The queue returned by `populate_queue` contains exactly the non-redundant
nodes of `l`, keyed by their resolved children (resolutions taken in the initial
state `s`, which is valid because children of `l`-nodes lie outside `l`).
-/
lemma populate_queue_queue {n m : Nat} (v : Vector (Node n m) m)
    (acc : List ((Pointer m × Pointer m) × Fin m)) (l : List (Fin m)) (s : State n m)
    (hstable : ∀ j ∈ l, (∀ j', v[j].low = node j' → j' ∉ l) ∧ (∀ j', v[j].high = node j' → j' ∉ l)) :
    ((populate_queue v acc l).run s).1 =
      (l.filterMap (fun j =>
        if resolveId s v[j].low = resolveId s v[j].high then none
        else some ((resolveId s v[j].low, resolveId s v[j].high), j))).reverse ++ acc := by
  -- We will prove the statement by induction on the list `l`. The base case is when `l` is empty.
  induction' l with j tail ih generalizing acc s; rfl
  rw [ populate_queue_cons_run, List.filterMap_cons ] ; simp +decide [ * ]
  split_ifs <;> simp +decide [ * ]
  · have h_filterMap_eq : ∀ j' ∈ tail, resolveId ⟨s.out, s.ids.set j (resolveId s v[j].high), s.nid⟩ v[j'].low = resolveId s v[j'].low ∧ resolveId ⟨s.out, s.ids.set j (resolveId s v[j].high), s.nid⟩ v[j'].high = resolveId s v[j'].high := by
      intro j' hj'
      have h_filterMap_eq : ∀ p : Pointer m, (∀ j'', p = node j'' → j'' ∉ j :: tail) → resolveId ⟨s.out, s.ids.set j (resolveId s v[j].high), s.nid⟩ p = resolveId s p := by
        intro p hp
        cases p with
        | terminal _ => rfl
        | node j'' =>
          have hmem : j'' ∉ j :: tail := hp j'' rfl
          simp only [List.mem_cons, not_or] at hmem
          exact Vector.getElem_set_ne j.2 j''.2 (Fin.val_ne_of_ne (Ne.symm hmem.1))
      exact ⟨ h_filterMap_eq _ fun j'' hj'' => hstable _ ( List.mem_cons_of_mem _ hj' ) |>.1 _ hj'', h_filterMap_eq _ fun j'' hj'' => hstable _ ( List.mem_cons_of_mem _ hj' ) |>.2 _ hj'' ⟩
    grind +suggestions
  · grind +suggestions

/-- One-step unfolding of `process_record`, expressed with `resolveId`. -/
lemma process_record_run {n m : Nat} (v : Vector (Node n.succ m.succ) m.succ)
    (curkey : Pointer m.succ × Pointer m.succ) (key : Pointer m.succ × Pointer m.succ)
    (j : Fin m.succ) (s : State n.succ m.succ) :
    (process_record v curkey (key, j)).run s =
      if key = curkey then
        (curkey, (⟨s.out, s.ids.set j (node s.nid), s.nid⟩ : State n.succ m.succ))
      else
        (key, (⟨s.out.set ((s.nid.1 + 1) % m.succ)
                ⟨v[j].var, resolveId s v[j].low, resolveId s v[j].high⟩
                (Nat.mod_lt _ (Nat.succ_pos _)),
              s.ids.set j (node (s.nid + 1)), s.nid + 1⟩ : State n.succ m.succ)) := by
  unfold process_record
  dsimp only
  split
  · simp only [StateT.run_bind, set_id_to_nid_run]; rfl
  · simp only [StateT.run_bind, get_id_run', set_out_run, set_id_to_nid_run]; rfl

/-- One-step unfolding of `process_queue` on a cons. -/
lemma process_queue_cons_run {n m : Nat} (v : Vector (Node n.succ m.succ) m.succ)
    (curkey : Pointer m.succ × Pointer m.succ)
    (head : (Pointer m.succ × Pointer m.succ) × Fin m.succ)
    (tail : List ((Pointer m.succ × Pointer m.succ) × Fin m.succ)) (s : State n.succ m.succ) :
    (process_queue v curkey (head :: tail)).run s =
      (process_queue v ((process_record v curkey head).run s).1 tail).run
        ((process_record v curkey head).run s).2 := by
  conv_lhs => unfold process_queue
  rw [StateT.run_bind]
  rfl

/-! ### A locally-ordered, downward-closed region of a heap is ordered

The imperative algorithm writes nodes into `out` in increasing slot order, where
every created node has strictly smaller variable than (and points only to)
previously-created nodes.  The following monad-free lemmas capture the
consequences of that structure: from any pointer into the created region
(`< c`), reachability stays inside the region, and the rooted sub-BDD is
ordered. -/

/-
From a pointer into the created region, reachability stays in the region.
-/
lemma reachable_region {n m : Nat} (w : Vector (Node (n+1) (m+1)) (m+1)) (c : Nat)
    (hchild : ∀ x : Fin (m+1), x.1 < c →
        (∀ j', w[x].low  = node j' → j'.1 < x.1) ∧ (∀ j', w[x].high = node j' → j'.1 < x.1))
    {p : Pointer (m+1)} (hp : ∀ j', p = node j' → j'.1 < c)
    {q : Pointer (m+1)} (hq : Reachable w p q) :
    ∀ j', q = node j' → j'.1 < c := by
  induction' hq with q' hq' ih
  · assumption
  · cases ‹Edge w q' hq'›; all_goals grind

/-
A locally-ordered, downward-closed region induces an ordered sub-BDD.
-/
lemma ordered_of_region {n m : Nat} (w : Vector (Node (n+1) (m+1)) (m+1)) (c : Nat)
    (hchild : ∀ x : Fin (m+1), x.1 < c →
        (∀ j', w[x].low  = node j' → j'.1 < x.1) ∧ (∀ j', w[x].high = node j' → j'.1 < x.1))
    (horder : ∀ x : Fin (m+1), x.1 < c →
        Pointer.MayPrecede w (node x) w[x].low ∧ Pointer.MayPrecede w (node x) w[x].high)
    {p : Pointer (m+1)} (hp : ∀ j', p = node j' → j'.1 < c) :
    Bdd.Ordered ⟨w, p⟩ := by
  intro ⟨ a, ha ⟩ ⟨ b, hb ⟩ e
  cases e
  · rename_i j hlow
    have hreach := reachable_region w c hchild hp ha
    have hmp := (horder j (hreach j rfl)).1
    rw [hlow] at hmp
    exact hmp
  · rename_i j hj
    have := reachable_region w c hchild hp ha j rfl
    have hmp := (horder j this).2
    rw [hj] at hmp
    exact hmp

/-
A locally-ordered, downward-closed, non-redundant, canonical region induces a
*reduced* sub-BDD.
-/
lemma reduced_of_region {n m : Nat} (w : Vector (Node (n+1) (m+1)) (m+1)) (c : Nat)
    (hchild : ∀ x : Fin (m+1), x.1 < c →
        (∀ j', w[x].low  = node j' → j'.1 < x.1) ∧ (∀ j', w[x].high = node j' → j'.1 < x.1))
    (horder : ∀ x : Fin (m+1), x.1 < c →
        Pointer.MayPrecede w (node x) w[x].low ∧ Pointer.MayPrecede w (node x) w[x].high)
    (hnored : ∀ x : Fin (m+1), x.1 < c → ¬ Pointer.Redundant w (node x))
    (hcanon : ∀ x y : Fin (m+1), x.1 < c → y.1 < c →
        ∀ (hox : Bdd.Ordered ⟨w, node x⟩) (hoy : Bdd.Ordered ⟨w, node y⟩),
          OBdd.toTree ⟨⟨w, node x⟩, hox⟩ = OBdd.toTree ⟨⟨w, node y⟩, hoy⟩ → x = y)
    {p : Pointer (m+1)} (hp : ∀ j', p = node j' → j'.1 < c) :
    OBdd.Reduced ⟨⟨w, p⟩, ordered_of_region w c hchild horder hp⟩ := by
  refine ⟨ ?_, ?_ ⟩
  · intro ⟨ x, hx ⟩
    cases x <;> simp +decide
    · cases hx
      · exact fun h => by cases h
      · cases ‹Edge _ _ _› ; tauto
        exact fun h => by cases h
    · exact hnored _ ( by simpa using reachable_region w c hchild hp hx _ rfl )
  · intro ⟨ a, ha ⟩ ⟨ b, hb ⟩ hab
    rcases a with ( _ | a ) <;> rcases b with ( _ | b )
    · unfold OBdd.SimilarRP at hab
      unfold OBdd.Similar at hab
      unfold OBdd.HSimilar at hab
      simp_all [InvImage, OBdd.toTree_terminal]
    · unfold OBdd.SimilarRP at hab
      unfold OBdd.Similar at hab
      unfold OBdd.HSimilar at hab
      unfold OBdd.toTree at hab
      cases hab
    · contrapose! hab
      unfold OBdd.SimilarRP; simp +decide
      unfold OBdd.Similar; simp +decide [ OBdd.HSimilar ]
      rw [ OBdd.toTree_node ]
      exact fun h => by cases h
      rfl
    · specialize hcanon a b ( by
        exact reachable_region w c hchild hp ha a rfl ) ( by
        exact reachable_region w c hchild hp hb b rfl ) ( by
        apply ordered_of_region w c hchild horder
        exact reachable_region w c hchild hp ha ) ( by
        exact ordered_of_region w c hchild horder ( fun j' hj' => by
          convert reachable_region w c hchild hp hb j' hj' using 1 ) ) ( by
        convert hab using 1 )
      subst hcanon; rfl

/-- `OBdd.toTree` depends only on the underlying `Bdd` (the orderedness proof is
irrelevant). -/
lemma toTree_congr {n m : Nat} {O U : OBdd n m} (h : O.1 = U.1) :
    OBdd.toTree O = OBdd.toTree U := by
  obtain ⟨O, hO⟩ := O; obtain ⟨U, hU⟩ := U; cases h; rfl

/-- `toTree` of a node, expressed with its two children as explicit
pointer-rooted ordered sub-BDDs (any ordered witnesses). -/
lemma toTree_node_eq {n m : Nat} {w : Vector (Node n m) m} (x : Fin m)
    (hox : Bdd.Ordered ⟨w, node x⟩)
    (hl : Bdd.Ordered ⟨w, w[x].low⟩) (hh : Bdd.Ordered ⟨w, w[x].high⟩) :
    OBdd.toTree ⟨⟨w, node x⟩, hox⟩ =
      DecisionTree.branch w[x].var (OBdd.toTree ⟨⟨w, w[x].low⟩, hl⟩)
        (OBdd.toTree ⟨⟨w, w[x].high⟩, hh⟩) := by
  rw [OBdd.toTree_node (h := rfl)]
  exact congrArg₂ _ (toTree_congr rfl) (toTree_congr rfl)

/-
**Decoupling lemma.**  For a downward-closed region (`hchild`) whose created
nodes have pairwise-distinct `(var, low, high)` triples (`htriple`), the
`toTree`-canonicity condition required by `reduced_of_region` holds.  This lets the
imperative-algorithm invariant track only the elementary, decidable
*distinct-triples* property instead of `toTree` equality.
-/
lemma hcanon_of_triple {n m : Nat} (w : Vector (Node (n+1) (m+1)) (m+1)) (c : Nat)
    (hchild : ∀ x : Fin (m+1), x.1 < c →
        (∀ j', w[x].low  = node j' → j'.1 < x.1) ∧ (∀ j', w[x].high = node j' → j'.1 < x.1))
    (htriple : ∀ x y : Fin (m+1), x.1 < c → y.1 < c → w[x] = w[y] → x = y) :
    ∀ x y : Fin (m+1), x.1 < c → y.1 < c →
      ∀ (hox : Bdd.Ordered ⟨w, node x⟩) (hoy : Bdd.Ordered ⟨w, node y⟩),
        OBdd.toTree ⟨⟨w, node x⟩, hox⟩ = OBdd.toTree ⟨⟨w, node y⟩, hoy⟩ → x = y := by
  -- Pointer-level statement, with a nat fuel `N` bounding node indices, proved by
  -- induction on `N`.  Casing on the *pointer* (a plain variable) sidesteps the
  -- dependent-proof rewriting that blocks a direct node-level induction.
  suffices H : ∀ N : Nat, ∀ p q : Pointer (m+1),
      (∀ j', p = node j' → j'.1 < c ∧ j'.1 < N) → (∀ j', q = node j' → j'.1 < c) →
      ∀ (hop : Bdd.Ordered ⟨w, p⟩) (hoq : Bdd.Ordered ⟨w, q⟩),
        OBdd.toTree ⟨⟨w, p⟩, hop⟩ = OBdd.toTree ⟨⟨w, q⟩, hoq⟩ → p = q by
    intro x y hx hy hox hoy hxy
    have h := H (x.1 + 1) (node x) (node y)
      (by intro j' hj'; cases hj'; exact ⟨hx, Nat.lt_succ_self _⟩)
      (by intro j' hj'; cases hj'; exact hy) hox hoy hxy
    injection h
  intro N
  induction N with
  | zero =>
    intro p q hp hq hop hoq hpq
    rcases p with b | a
    · rcases q with b' | a'
      · rw [OBdd.toTree_terminal, OBdd.toTree_terminal] at hpq; injection hpq with hb; rw [hb]
      · rw [OBdd.toTree_terminal, toTree_node_eq a' hoq (Bdd.low_ordered rfl hoq)
            (Bdd.high_ordered rfl hoq)] at hpq; simp at hpq
    · exact absurd (hp a rfl).2 (Nat.not_lt_zero _)
  | succ N ih =>
    intro p q hp hq hop hoq hpq
    rcases p with b | a <;> rcases q with b' | a'
    · rw [OBdd.toTree_terminal, OBdd.toTree_terminal] at hpq; injection hpq with hb; rw [hb]
    · rw [OBdd.toTree_terminal, toTree_node_eq a' hoq (Bdd.low_ordered rfl hoq)
          (Bdd.high_ordered rfl hoq)] at hpq; simp at hpq
    · rw [OBdd.toTree_terminal, toTree_node_eq a hop (Bdd.low_ordered rfl hop)
          (Bdd.high_ordered rfl hop)] at hpq; simp at hpq
    · have haC : a.1 < c := (hp a rfl).1
      have haN : a.1 < N + 1 := (hp a rfl).2
      have ha'C : a'.1 < c := hq a' rfl
      rw [toTree_node_eq a hop (Bdd.low_ordered rfl hop) (Bdd.high_ordered rfl hop),
          toTree_node_eq a' hoq (Bdd.low_ordered rfl hoq) (Bdd.high_ordered rfl hoq)] at hpq
      injection hpq with hv hl hh
      have hlow : w[a].low = w[a'].low :=
        ih (w[a].low) (w[a'].low)
          (by intro j' hj'; exact ⟨lt_trans ((hchild a haC).1 j' hj') haC,
                by have := (hchild a haC).1 j' hj'; linarith⟩)
          (by intro j' hj'; exact lt_trans ((hchild a' ha'C).1 j' hj') ha'C) _ _ hl
      have hhigh : w[a].high = w[a'].high :=
        ih (w[a].high) (w[a'].high)
          (by intro j' hj'; exact ⟨lt_trans ((hchild a haC).2 j' hj') haC,
                by have := (hchild a haC).2 j' hj'; linarith⟩)
          (by intro j' hj'; exact lt_trans ((hchild a' ha'C).2 j' hj') ha'C) _ _ hh
      have hnode : a = a' := htriple a a' haC ha'C (by
        have e1 : w[a] = (⟨w[a].var, w[a].low, w[a].high⟩ : Node _ _) := rfl
        have e2 : w[a'] = (⟨w[a'].var, w[a'].low, w[a'].high⟩ : Node _ _) := rfl
        rw [e1, e2, hv, hlow, hhigh])
      rw [hnode]

/-- The combined invariant maintained by `loop`.

`t` records that all reachable original nodes whose variable index is `≥ t` have
been processed; `c` is the number of nodes written to `out` so far (the created
region is the set of slots `< c`). -/
structure Inv {n m : Nat} (O : OBdd (n+1) (m+1)) (s : State (n+1) (m+1)) (t : Nat) (c : Nat) :
    Prop where
  /-- The write counter wraps around `m+1`; `c` writes leave it at `(m + c) % (m+1)`. -/
  hcle   : c ≤ m + 1
  hnid   : s.nid.1 = (m + c) % (m + 1)
  /-- Created nodes only point to strictly-earlier created nodes (or terminals). -/
  hchild : ∀ x : Fin (m+1), x.1 < c →
      (∀ j', s.out[x].low  = node j' → j'.1 < x.1) ∧ (∀ j', s.out[x].high = node j' → j'.1 < x.1)
  /-- No created node is redundant. -/
  hnored : ∀ x : Fin (m+1), x.1 < c → ¬ Pointer.Redundant s.out (node x)
  /-- Created nodes respect the variable ordering of their outgoing edges. -/
  horder : ∀ x : Fin (m+1), x.1 < c →
      Pointer.MayPrecede s.out (node x) s.out[x].low ∧
      Pointer.MayPrecede s.out (node x) s.out[x].high
  /-- Distinct created slots have distinct `(var, low, high)` triples (canonicity). -/
  htriple : ∀ x y : Fin (m+1), x.1 < c → y.1 < c → s.out[x] = s.out[y] → x = y
  /-- Every created slot is the image of some reachable, already-processed node. -/
  hsurj  : ∀ x : Fin (m+1), x.1 < c →
      ∃ j : Fin (m+1), Reachable O.1.heap O.1.root (node j) ∧ t ≤ O.1.heap[j].var.1 ∧ s.ids[j] = node x
  /-- Processed nodes are represented faithfully (same Boolean function), inside the
  created region, and the representative's variable is no earlier than the source's. -/
  hrepr  : ∀ j : Fin (m+1), (hj : Reachable O.1.heap O.1.root (node j)) → t ≤ O.1.heap[j].var.1 →
      (∀ j', s.ids[j] = node j' → j'.1 < c) ∧
      O.1.heap[j].var.1 ≤ (Pointer.toVar s.out s.ids[j]).1 ∧
      ∀ ho : Bdd.Ordered ⟨s.out, s.ids[j]⟩,
        OBdd.evaluate ⟨⟨s.out, s.ids[j]⟩, ho⟩
          = OBdd.evaluate ⟨⟨O.1.heap, node j⟩, Bdd.ordered_of_reachable hj⟩

/-- The `toTree`-canonicity condition, derived from the distinct-triples field via
`hcanon_of_triple`. -/
lemma Inv_hcanon {n m : Nat} {O : OBdd (n+1) (m+1)} {s : State (n+1) (m+1)} {t c : Nat}
    (inv : Inv O s t c) :
    ∀ x y : Fin (m+1), x.1 < c → y.1 < c →
      ∀ (hox : Bdd.Ordered ⟨s.out, node x⟩) (hoy : Bdd.Ordered ⟨s.out, node y⟩),
        OBdd.toTree ⟨⟨s.out, node x⟩, hox⟩ = OBdd.toTree ⟨⟨s.out, node y⟩, hoy⟩ → x = y :=
  hcanon_of_triple s.out c inv.hchild inv.htriple

/-! ## Correctness of the imperative `reduce`

The imperative `reduce` routine above is the runtime-efficient way to turn an
ordered BDD into an equivalent reduced one (it runs in (roughly) linear time in
the number of nodes, whereas the canonical construction of `Bdd.Canonical`
builds a heap of doubly-exponential size).

The algorithm is verified directly: the result is ordered, reduced, and denotes
the same Boolean function as the input. -/

/-! ### `keyLe` is a total preorder, so `mergeSort` groups equal keys

Sorting the dedup queue with `keyLe` produces a `keyLe`-sorted permutation of the
input.  Since `keyLe` is total, all records with equal `(low, high)` keys end up
contiguous, which is what `process_queue`'s adjacent-merge relies on. -/

/-- Reflexivity of the `Pointer` order (local helper). -/
private lemma ptrLe_refl (p : Pointer m) : p ≤ p := by
  cases p with
  | terminal b => exact Pointer.le.terminal_le_terminal (_root_.le_refl b)
  | node j => exact Pointer.le.node_le_node (_root_.le_refl j)

/-- Transitivity of the `Pointer` order (local helper). -/
private lemma ptrLe_trans {p q r : Pointer m} : p ≤ q → q ≤ r → p ≤ r := by
  intro h1 h2
  cases h1 <;> cases h2
  · rename_i b c hbc d hcd; exact Pointer.le.terminal_le_terminal (_root_.le_trans hbc hcd)
  · exact Pointer.le.terminal_le_node
  · exact Pointer.le.terminal_le_node
  · rename_i j i hji k hik; exact Pointer.le.node_le_node (_root_.le_trans hji hik)

/-- Totality of the `Pointer` order (local helper). -/
private lemma ptrLe_total (p q : Pointer m) : p ≤ q ∨ q ≤ p := by
  cases p <;> cases q
  · rename_i b c
    rcases _root_.le_total b c with h | h
    · exact Or.inl (Pointer.le.terminal_le_terminal h)
    · exact Or.inr (Pointer.le.terminal_le_terminal h)
  · exact Or.inl Pointer.le.terminal_le_node
  · exact Or.inr Pointer.le.terminal_le_node
  · rename_i j i
    rcases _root_.le_total j i with h | h
    · exact Or.inl (Pointer.le.node_le_node h)
    · exact Or.inr (Pointer.le.node_le_node h)

/-- Antisymmetry of the `Pointer` order (local helper). -/
private lemma ptrLe_antisymm {p q : Pointer m} : p ≤ q → q ≤ p → p = q := by
  intro h1 h2
  cases h1 <;> cases h2
  · rename_i b c hbc hcb; exact congrArg _ (_root_.le_antisymm hbc hcb)
  · rename_i j i hji hij; exact congrArg _ (_root_.le_antisymm hji hij)

/-
`keyLe` is transitive.
-/
private lemma keyLe_trans {m : Nat} (a b c : (Pointer m × Pointer m) × Fin m) :
    keyLe a b = true → keyLe b c = true → keyLe a c = true := by
  unfold keyLe
  split_ifs <;> simp_all +decide
  grind +suggestions
  · exact fun h₁ h₂ => False.elim <| ‹¬b.1.2 = c.1.2› <| ptrLe_antisymm h₂ h₁
  · exact fun h₁ h₂ => ptrLe_trans h₁ h₂
  · exact fun h₁ h₂ => False.elim <| ‹¬c.1.1 = b.1.1› <| ptrLe_antisymm h₁ h₂
  · exact fun h₁ h₂ => False.elim <| ‹¬c.1.1 = b.1.1› <| ptrLe_antisymm h₁ h₂
  · exact fun h₁ h₂ => ptrLe_trans h₁ h₂

/-
`keyLe` is total.
-/
private lemma keyLe_total {m : Nat} (a b : (Pointer m × Pointer m) × Fin m) :
    (keyLe a b || keyLe b a) = true := by
  unfold keyLe
  split_ifs <;> simp_all +decide [ ptrLe_total ]
  grind +suggestions

/-- `mergeSort` with `keyLe` produces a `keyLe`-sorted list. -/
private lemma mergeSort_keyLe_sorted {m : Nat} (Q : List ((Pointer m × Pointer m) × Fin m)) :
    List.Pairwise (fun a b => keyLe a b = true) (List.mergeSort Q keyLe) :=
  List.pairwise_mergeSort keyLe_trans keyLe_total Q

/-- `mergeSort` with `keyLe` is a permutation of its input. -/
private lemma mergeSort_keyLe_perm {m : Nat} (Q : List ((Pointer m × Pointer m) × Fin m)) :
    (List.mergeSort Q keyLe).Perm Q :=
  List.mergeSort_perm Q keyLe

/-! ### A pure model of `process_queue`

`processFold` is the pure state-transformer that `process_queue` runs.  It folds
the (already-proven) one-step pure effect `process_record_run` over the queue,
threading the running `curkey`.  `process_queue_run` certifies it. -/

/-- The pure state-transformer computed by `process_queue`. -/
private def processFold {n m : Nat} (v : Vector (Node n.succ m.succ) m.succ) :
    Pointer m.succ × Pointer m.succ → State n.succ m.succ →
    List ((Pointer m.succ × Pointer m.succ) × Fin m.succ) → State n.succ m.succ
  | _, s, [] => s
  | curkey, s, (key, j) :: tail =>
    if key = curkey then
      processFold v curkey ⟨s.out, s.ids.set j (node s.nid), s.nid⟩ tail
    else
      processFold v key
        ⟨s.out.set ((s.nid.1 + 1) % m.succ)
            ⟨v[j].var, resolveId s v[j].low, resolveId s v[j].high⟩
            (Nat.mod_lt _ (Nat.succ_pos _)),
          s.ids.set j (node (s.nid + 1)), s.nid + 1⟩ tail

/-
`process_queue` runs the pure `processFold`.
-/
private lemma process_queue_run {n m : Nat} (v : Vector (Node n.succ m.succ) m.succ)
    (curkey : Pointer m.succ × Pointer m.succ)
    (L : List ((Pointer m.succ × Pointer m.succ) × Fin m.succ)) (s : State n.succ m.succ) :
    (process_queue v curkey L).run s = ((), processFold v curkey s L) := by
  induction' L with key j L ih generalizing s curkey <;> simp_all +decide [ processFold ]
  · rfl
  · rw [process_queue_cons_run]
    rw [process_record_run]; split <;> exact L _ _ _

/-- The number of *new* (non-redundant) nodes `processFold` creates: one per
maximal run of equal keys.  `curkey` is the key carried in from the previous
record. -/
private def newKeyCount {m : Nat} :
    Pointer m.succ × Pointer m.succ →
    List ((Pointer m.succ × Pointer m.succ) × Fin m.succ) → Nat
  | _, [] => 0
  | curkey, (key, _) :: tail =>
    if key = curkey then newKeyCount curkey tail else newKeyCount key tail + 1

/-
`processFold` advances `nid` by exactly `newKeyCount` (modulo `m+1`).
-/
private lemma processFold_nid {n m : Nat} (v : Vector (Node n.succ m.succ) m.succ)
    (curkey : Pointer m.succ × Pointer m.succ)
    (L : List ((Pointer m.succ × Pointer m.succ) × Fin m.succ)) (s : State n.succ m.succ) :
    (processFold v curkey s L).nid.1 = (s.nid.1 + newKeyCount curkey L) % (m + 1) := by
  induction' L with key j L ih generalizing s curkey
  · exact Eq.symm ( Nat.mod_eq_of_lt ( show s.nid.1 < m + 1 from s.nid.2 ) )
  · by_cases h : key.1 = curkey <;> simp_all +decide [ processFold, newKeyCount ]
    simp +decide [ add_comm, add_assoc, Fin.val_add ]

/-
`processFold` leaves `ids[k]` unchanged for indices `k` not appearing in the
queue `L`.
-/
private lemma processFold_ids_ne {n m : Nat} (v : Vector (Node n.succ m.succ) m.succ)
    (curkey : Pointer m.succ × Pointer m.succ)
    (L : List ((Pointer m.succ × Pointer m.succ) × Fin m.succ)) (s : State n.succ m.succ)
    (k : Fin m.succ) (hk : k ∉ L.map (·.2)) :
    (processFold v curkey s L).ids[k] = s.ids[k] := by
  induction' L with key j L ih generalizing s curkey
  · rfl
  · unfold processFold; simp +decide [ * ]
    split_ifs <;> simp_all +decide; all_goals grind

/-! ## The loop-invariant correctness development

The correctness of `reduce` rests on the loop invariant `Inv` and the inner-loop
invariant `PInv`: `Inv` is established at `initial`, preserved by each `step`
(one variable level) via `step_Inv`, and therefore holds at loop termination
(`loop_Inv`).  The four correctness obligations about `reduce` are read off the
final invariant. -/

/-! ### The loop invariant is established and maintained

The imperative `reduce` runs `loop` from `initial`.  The three lemmas below
set up the loop invariant `Inv`: it holds initially, is preserved by each `step`
(one variable level), and therefore holds at loop termination, where the
returned `Bdd` is read off the final state. -/

/-
`initial` establishes the invariant: nothing has been created (`c = 0`) and
no reachable node has variable index `≥ n+1`, so all obligations are vacuous.
-/
lemma initial_Inv {n m : Nat} (O : OBdd (n+1) (m+1)) : Inv O initial (n+1) 0 := by
  refine' ⟨ _, _, _, _, _, _, _, _ ⟩ <;> norm_num [ initial ]
  grind +suggestions

/-- The post-`step` state: run `populate_queue` to get the dedup queue and the
intermediate state, then run the pure `processFold` over the `keyLe`-sorted
queue. -/
lemma step_run {n m : Nat} (v : Vector (Node (n+1) (m+1)) (m+1))
    (vlist : Vector (List (Fin (m+1))) (n+1)) (i : Fin (n+1)) (s : State (n+1) (m+1)) :
    (StateT.run (step v vlist i) s).2 =
      processFold v ⟨node 0, node 0⟩ ((populate_queue v [] vlist[i]).run s).2
        (List.mergeSort ((populate_queue v [] vlist[i]).run s).1 keyLe) := by
  unfold step
  rw [StateT.run_bind]
  simp only [process_queue_run]
  rfl

/-! ### A total order on dedup-key pairs

`pairLe` is the lexicographic order on `(low, high)` pairs (the dedup key,
forgetting the node index).  Records with equal pairs are isomorphic and are
merged by `process_queue`; sorting with `keyLe` (which refines `pairLe` by the
node index) places equal pairs contiguously. -/

private def pairLe {m : Nat} (p q : Pointer (m+1) × Pointer (m+1)) : Prop :=
  if p.1 = q.1 then p.2 ≤ q.2 else p.1 ≤ q.1

private lemma pairLe_refl {m : Nat} (p : Pointer (m+1) × Pointer (m+1)) : pairLe p p := by
  unfold pairLe; rw [if_pos rfl]; exact ptrLe_refl _

private lemma pairLe_total {m : Nat} (p q : Pointer (m+1) × Pointer (m+1)) :
    pairLe p q ∨ pairLe q p := by
  unfold pairLe
  by_cases h : p.1 = q.1
  · rw [if_pos h, if_pos h.symm]; exact ptrLe_total _ _
  · rw [if_neg h, if_neg (Ne.symm h)]; exact ptrLe_total _ _

private lemma pairLe_antisymm {m : Nat} {p q : Pointer (m+1) × Pointer (m+1)}
    (h1 : pairLe p q) (h2 : pairLe q p) : p = q := by
  unfold pairLe at h1 h2
  by_cases h : p.1 = q.1
  · rw [if_pos h] at h1; rw [if_pos h.symm] at h2
    exact Prod.ext h (ptrLe_antisymm h1 h2)
  · rw [if_neg h] at h1; rw [if_neg (Ne.symm h)] at h2
    exact absurd (ptrLe_antisymm h1 h2) h

private lemma pairLe_trans {m : Nat} {p q r : Pointer (m+1) × Pointer (m+1)}
    (h1 : pairLe p q) (h2 : pairLe q r) : pairLe p r := by
  unfold pairLe at *
  split_ifs at * <;> try exact ptrLe_trans h1 h2
  all_goals simp_all +decide
  exact False.elim <| ‹¬r.1 = q.1› <| ptrLe_antisymm h1 h2

/-
`keyLe` refines `pairLe`: a `keyLe`-sorted list is `pairLe`-sorted on the
key pairs.
-/
private lemma pairLe_of_keyLe {m : Nat} {a b : (Pointer (m+1) × Pointer (m+1)) × Fin (m+1)}
    (h : keyLe a b = true) : pairLe a.1 b.1 := by
  unfold keyLe at h
  unfold pairLe; split_ifs at h <;> simp_all +decide [ ptrLe_refl ]

/-- If `a ≤ b` and `b < r` (i.e. `b ≤ r` with `r ≠ b`) in the `pairLe` order, then
`a ≠ r`.  Used to derive strict monotonicity of new key pairs. -/
private lemma pairLe_ne_of_le_lt {m : Nat} {a b r : Pointer (m+1) × Pointer (m+1)}
    (h1 : pairLe a b) (h2 : pairLe b r) (hne : r ≠ b) : a ≠ r := by
  intro heq; apply hne; rw [heq] at h1; exact pairLe_antisymm h1 h2

/-! ### The `processFold` (inner-loop) invariant

`PInv v lev cbase obase curkey s c` is the invariant maintained while
`process_queue`/`processFold` consumes one variable level's dedup queue.
`obase` is the `out` vector when the level started; the old region `[0, cbase)`
is frozen, and new nodes `[cbase, c)` all have variable `lev`, point only into
the old region, are non-redundant, and have strictly-increasing (hence distinct)
key pairs, the largest being `curkey`. -/
structure PInv {n m : Nat} (v : Vector (Node (n+1) (m+1)) (m+1)) (lev : Nat) (cbase : Nat)
    (obase : Vector (Node (n+1) (m+1)) (m+1))
    (curkey : Pointer (m+1) × Pointer (m+1)) (s : State (n+1) (m+1)) (c : Nat) : Prop where
  cle   : c ≤ m + 1
  cge   : cbase ≤ c
  nid   : s.nid.1 = (m + c) % (m + 1)
  frame : ∀ x : Fin (m+1), x.1 < cbase → s.out[x] = obase[x]
  child : ∀ x : Fin (m+1), x.1 < c →
      (∀ j', s.out[x].low = node j' → j'.1 < x.1) ∧ (∀ j', s.out[x].high = node j' → j'.1 < x.1)
  nored : ∀ x : Fin (m+1), x.1 < c → s.out[x].low ≠ s.out[x].high
  newvar : ∀ x : Fin (m+1), cbase ≤ x.1 → x.1 < c → s.out[x].var.1 = lev
  newlow : ∀ x : Fin (m+1), cbase ≤ x.1 → x.1 < c → (∀ j', s.out[x].low = node j' → j'.1 < cbase)
  newhigh : ∀ x : Fin (m+1), cbase ≤ x.1 → x.1 < c → (∀ j', s.out[x].high = node j' → j'.1 < cbase)
  /-- New key pairs are strictly increasing in `pairLe`. -/
  mono  : ∀ x y : Fin (m+1), cbase ≤ x.1 → x.1 < y.1 → y.1 < c →
      pairLe (s.out[x].low, s.out[x].high) (s.out[y].low, s.out[y].high) ∧
      (s.out[x].low, s.out[x].high) ≠ (s.out[y].low, s.out[y].high)
  /-- The most recent new node carries the running key `curkey`. -/
  curlink : ∀ x : Fin (m+1), cbase < c → x.1 + 1 = c →
      s.out[x].low = curkey.1 ∧ s.out[x].high = curkey.2
  /-- All new key pairs are ≤ `curkey`. -/
  curmax : ∀ x : Fin (m+1), cbase ≤ x.1 → x.1 < c →
      pairLe (s.out[x].low, s.out[x].high) curkey

/-
`processFold` only writes to slots `≥ c` (the current write frontier), so the
region below `c` is frozen, provided the run does not wrap the counter.
-/
lemma processFold_out_old {n m : Nat} (v : Vector (Node (n+1) (m+1)) (m+1))
    (curkey : Pointer (m+1) × Pointer (m+1))
    (L : List ((Pointer (m+1) × Pointer (m+1)) × Fin (m+1))) (s : State (n+1) (m+1)) (c : Nat)
    (hnid : s.nid.1 = (m + c) % (m + 1)) (hc : c ≤ m + 1)
    (hbound : c + newKeyCount curkey L ≤ m + 1) :
    ∀ x : Fin (m+1), x.1 < c → (processFold v curkey s L).out[x] = s.out[x] := by
  intro x hx
  induction' L with key j L ih generalizing s curkey c
  · rfl
  · by_cases h : key.1 = curkey <;> simp_all +decide [ processFold, newKeyCount ]
    · grind
    · convert L _ _ _ ( c + 1 ) _ _ _ _ using 1
      · simp +decide [ Vector.getElem_set]
        intro h; have := Nat.mod_add_div ( m + c + 1 ) ( m + 1 ) ; simp_all +decide
        nlinarith [ show ( m + c + 1 ) / ( m + 1 ) = 1 by nlinarith ]
      · simp +decide [ ← add_assoc, Fin.val_add ]
        simp +decide [ hnid, Nat.add_mod ]
      · grind
      · grind
      · lia

/-
Counter arithmetic for one write: from `nid = (m+c) % (m+1)` with `c ≤ m`,
the next write slot is `c` and the new counter region is `c`.
-/
private lemma nid_arith {m c : Nat} (hc : c ≤ m) :
    ((m + c) % (m + 1) + 1) % (m + 1) = c ∧ (m + (c + 1)) % (m + 1) = c := by
  cases hc.eq_or_lt <;> simp_all +arith +decide [ ]
  · norm_num [ ( by ring : 2 * m + 1 = m + ( m + 1 ) ) ]
  · norm_num [ ( by ring : m + c + 1 = m + 1 + c ) ]
    linarith

/-
The strict-monotonicity (`mono`) field for the post-write state of a single
*create*: with the new node written at slot `(s.nid.1+1)%(m+1) = c`, the new key
pairs in `[cbase, c+1)` are strictly increasing in `pairLe`.
-/
private lemma PInv_create_mono {n m : Nat} (v : Vector (Node (n+1) (m+1)) (m+1)) (lev : Nat)
    (cbase : Nat) (obase : Vector (Node (n+1) (m+1)) (m+1))
    (curkey : Pointer (m+1) × Pointer (m+1)) (s : State (n+1) (m+1)) (c : Nat)
    (key : Pointer (m+1) × Pointer (m+1)) (j : Fin (m+1))
    (hpi : PInv v lev cbase obase curkey s c)
    (hslot : (s.nid.1 + 1) % (m + 1) = c)
    (hne : key ≠ curkey)
    (hcur : cbase < c → pairLe curkey key)
    (hres1 : resolveId s v[j].low = key.1) (hres2 : resolveId s v[j].high = key.2) :
    ∀ x y : Fin (m+1), cbase ≤ x.1 → x.1 < y.1 → y.1 < c + 1 →
      pairLe
        ((s.out.set ((s.nid.1 + 1) % (m + 1))
            ⟨v[j].var, resolveId s v[j].low, resolveId s v[j].high⟩
            (Nat.mod_lt _ (Nat.succ_pos _)))[x].low,
         (s.out.set ((s.nid.1 + 1) % (m + 1))
            ⟨v[j].var, resolveId s v[j].low, resolveId s v[j].high⟩
            (Nat.mod_lt _ (Nat.succ_pos _)))[x].high)
        ((s.out.set ((s.nid.1 + 1) % (m + 1))
            ⟨v[j].var, resolveId s v[j].low, resolveId s v[j].high⟩
            (Nat.mod_lt _ (Nat.succ_pos _)))[y].low,
         (s.out.set ((s.nid.1 + 1) % (m + 1))
            ⟨v[j].var, resolveId s v[j].low, resolveId s v[j].high⟩
            (Nat.mod_lt _ (Nat.succ_pos _)))[y].high) ∧
      ((s.out.set ((s.nid.1 + 1) % (m + 1))
            ⟨v[j].var, resolveId s v[j].low, resolveId s v[j].high⟩
            (Nat.mod_lt _ (Nat.succ_pos _)))[x].low,
         (s.out.set ((s.nid.1 + 1) % (m + 1))
            ⟨v[j].var, resolveId s v[j].low, resolveId s v[j].high⟩
            (Nat.mod_lt _ (Nat.succ_pos _)))[x].high) ≠
      ((s.out.set ((s.nid.1 + 1) % (m + 1))
            ⟨v[j].var, resolveId s v[j].low, resolveId s v[j].high⟩
            (Nat.mod_lt _ (Nat.succ_pos _)))[y].low,
         (s.out.set ((s.nid.1 + 1) % (m + 1))
            ⟨v[j].var, resolveId s v[j].low, resolveId s v[j].high⟩
            (Nat.mod_lt _ (Nat.succ_pos _)))[y].high) := by
  intro x y hx hy hxy
  by_cases hyN : y.1 = c
  · simp_all +decide [ Vector.getElem_set]
    have := hpi.curmax x hx ( by linarith ) ; split_ifs <;> simp_all +decide
    exact ⟨ pairLe_trans this ( hcur ( by linarith ) ), fun h => hne <| by have := pairLe_antisymm this ( hcur ( by linarith ) |> fun h => by grind ) ; grind ⟩
  · -- Since y.1 < c, both x and y are in the range where the entries are unchanged.
    have hx_lt_c : x.1 < c := by
      omega
    have hy_lt_c : y.1 < c := by
      exact lt_of_le_of_ne ( Nat.le_of_lt_succ hxy ) hyN
    have := hpi.mono x y hx hy hy_lt_c; simp_all +decide [ Vector.getElem_set ]
    lia

/-
A single *create* record (a new key) extends `PInv` by one node.
-/
lemma PInv_create {n m : Nat} (v : Vector (Node (n+1) (m+1)) (m+1)) (lev : Nat)
    (cbase : Nat) (obase : Vector (Node (n+1) (m+1)) (m+1))
    (curkey : Pointer (m+1) × Pointer (m+1)) (s : State (n+1) (m+1)) (c : Nat)
    (key : Pointer (m+1) × Pointer (m+1)) (j : Fin (m+1))
    (hpi : PInv v lev cbase obase curkey s c)
    (hbound : c + 1 ≤ m + 1)
    (hslot : (s.nid.1 + 1) % (m + 1) = c)
    (hne : key ≠ curkey)
    (hcur : cbase < c → pairLe curkey key)
    (hkl : key.1 ≠ key.2)
    (hklow : ∀ j', key.1 = node j' → j'.1 < cbase)
    (hkhigh : ∀ j', key.2 = node j' → j'.1 < cbase)
    (hvar : v[j].var.1 = lev)
    (hres1 : resolveId s v[j].low = key.1) (hres2 : resolveId s v[j].high = key.2) :
    PInv v lev cbase obase key
      ⟨s.out.set ((s.nid.1 + 1) % (m + 1))
          ⟨v[j].var, resolveId s v[j].low, resolveId s v[j].high⟩ (Nat.mod_lt _ (Nat.succ_pos _)),
        s.ids.set j (node (s.nid + 1)), s.nid + 1⟩ (c + 1) := by
  constructor
  any_goals linarith [ hpi.cge ]
  any_goals rw [ Fin.val_add ] ; simp +decide [ hslot ]
  any_goals rw [ ← hslot ] ; exact nid_arith ( by linarith ) |>.2.symm
  simp +decide [ Vector.getElem_set, hslot ] at *
  exact fun x hx => by rw [ if_neg ( by linarith [ hpi.cge ] ) ] ; exact hpi.frame x hx
  intro x hx
  by_cases hx : x = ⟨ c, by linarith ⟩ <;> simp_all +decide [ Vector.getElem_set ]
  exact ⟨ fun j' hj' => lt_of_lt_of_le ( hklow j' hj' ) ( by linarith [ hpi.cge ] ), fun j' hj' => lt_of_lt_of_le ( hkhigh j' hj' ) ( by linarith [ hpi.cge ] ) ⟩
  split_ifs <;> simp_all +decide [ Fin.ext_iff ]
  exact hpi.child x ( lt_of_le_of_ne ‹_› hx )
  intro x hx; by_cases hx' : x = ⟨ c, by linarith ⟩ <;> simp_all +decide [ Vector.getElem_set ]
  split_ifs <;> simp_all +decide [ Fin.ext_iff ]
  exact hpi.nored x ( lt_of_le_of_ne hx hx' )
  intro x hx₁ hx₂; by_cases hx₃ : x = ⟨ c, by linarith ⟩ <;> simp_all +decide [ Vector.getElem_set ]
  split_ifs <;> simp_all +decide [ Fin.ext_iff ]
  exact hpi.newvar x hx₁ ( lt_of_le_of_ne hx₂ hx₃ )
  · intro x hx₁ hx₂ j' hj'; by_cases hx₃ : x = ⟨ c, by linarith ⟩ <;> simp_all +decide [ Vector.getElem_set ]
    split_ifs at hj' <;> simp_all +decide [ Fin.ext_iff ]
    exact hpi.newlow x hx₁ ( lt_of_le_of_ne hx₂ hx₃ ) j' hj'
  · intro x hx₁ hx₂ j' hj'; by_cases hx₃ : x = ⟨ c, by linarith ⟩ <;> simp_all +decide [ Vector.getElem_set ]
    split_ifs at hj' <;> simp_all +decide [ Fin.ext_iff ]
    exact hpi.newhigh x hx₁ ( lt_of_le_of_ne hx₂ hx₃ ) j' hj'
  · apply PInv_create_mono v lev cbase obase curkey s c key j hpi hslot hne hcur hres1 hres2
  · intro x hx₁ hx₂; simp_all +decide
  · intro x hx₁ hx₂; by_cases hx₃ : x = ⟨ c, by linarith ⟩ <;> simp_all +decide [ Vector.getElem_set ]
    · exact pairLe_refl _
    · split_ifs <;> simp_all +decide [ Fin.ext_iff ]
      exact pairLe_trans ( hpi.curmax x hx₁ ( lt_of_le_of_ne hx₂ hx₃ ) ) ( hcur ( by omega ) )

/-- `PInv` reads only the `out` and `nid` components of the state, so an `ids`
write (the *merge* step) preserves it verbatim. -/
lemma PInv_set_ids {n m : Nat} (v : Vector (Node (n+1) (m+1)) (m+1)) (lev : Nat)
    (cbase : Nat) (obase : Vector (Node (n+1) (m+1)) (m+1))
    (curkey : Pointer (m+1) × Pointer (m+1)) (s : State (n+1) (m+1)) (c : Nat)
    (j : Fin (m+1)) (p : Pointer (m+1))
    (hpi : PInv v lev cbase obase curkey s c) :
    PInv v lev cbase obase curkey ⟨s.out, s.ids.set j p, s.nid⟩ c :=
  { cle := hpi.cle, cge := hpi.cge, nid := hpi.nid, frame := hpi.frame,
    child := hpi.child, nored := hpi.nored, newvar := hpi.newvar, newlow := hpi.newlow,
    newhigh := hpi.newhigh, mono := hpi.mono, curlink := hpi.curlink, curmax := hpi.curmax }

/-
`processFold` over a `keyLe`-sorted, non-redundant queue preserves `PInv`,
advancing the created-region counter by exactly `newKeyCount`.  (The companion
`processFold_rep` shows every queued node is represented.)
-/
lemma processFold_PInv_pres {n m : Nat} (v : Vector (Node (n+1) (m+1)) (m+1)) (lev : Nat)
    (cbase : Nat) (obase : Vector (Node (n+1) (m+1)) (m+1))
    (L : List ((Pointer (m+1) × Pointer (m+1)) × Fin (m+1)))
    (curkey : Pointer (m+1) × Pointer (m+1)) (s : State (n+1) (m+1)) (c : Nat)
    (hpi : PInv v lev cbase obase curkey s c)
    (hsorted : L.Pairwise (fun a b => keyLe a b = true))
    (hbound : c + newKeyCount curkey L ≤ m + 1)
    (hcur : cbase < c → ∀ a ∈ L, pairLe curkey a.1)
    (hfresh : cbase = c → ∀ a ∈ L, curkey ≠ a.1)
    (hnored : ∀ a ∈ L, a.1.1 ≠ a.1.2)
    (hkey : ∀ a ∈ L, resolveId s v[a.2].low = a.1.1 ∧ resolveId s v[a.2].high = a.1.2)
    (hold : ∀ a ∈ L, (∀ j', a.1.1 = node j' → j'.1 < cbase) ∧ (∀ j', a.1.2 = node j' → j'.1 < cbase))
    (hvarj : ∀ a ∈ L, v[a.2].var.1 = lev)
    (hnodupL : (L.map (·.2)).Nodup)
    (hstable : ∀ a ∈ L, (∀ j', v[a.2].low = node j' → j' ∉ L.map (·.2)) ∧
        (∀ j', v[a.2].high = node j' → j' ∉ L.map (·.2))) :
    ∃ ck',
      PInv v lev cbase obase ck' (processFold v curkey s L) (c + newKeyCount curkey L) := by
  induction' L with a L ih generalizing curkey s c
  · exact ⟨ curkey, by simpa using hpi ⟩
  · unfold newKeyCount at hbound ⊢
    split_ifs at hbound ⊢
    · specialize ih curkey ⟨s.out, s.ids.set a.2 (node s.nid), s.nid⟩ c (PInv_set_ids v lev cbase obase curkey s c a.2 (node s.nid) hpi) (List.pairwise_cons.mp hsorted |>.2) hbound (fun h x hx => hcur h x (List.mem_cons_of_mem _ hx)) (fun h x hx => hfresh h x (List.mem_cons_of_mem _ hx)) (fun x hx => hnored x (List.mem_cons_of_mem _ hx)) (by
      intro b hb
      convert hkey b ( List.mem_cons_of_mem _ hb ) using 1
      · rw [ resolveId_set_ids_ne ]
        grind
      · rw [ resolveId_set_ids_ne ]
        exact fun k hk => fun hk' => hstable b ( List.mem_cons_of_mem _ hb ) |>.2 k hk ( by simp +decide [ hk' ] )) (fun x hx => hold x (List.mem_cons_of_mem _ hx)) (fun x hx => hvarj x (List.mem_cons_of_mem _ hx)) (by
      exact List.Nodup.of_cons hnodupL) (fun b hb => by
        grind)
      unfold processFold; grind
    · have hL : c ≤ m ∧ (s.nid.1 + 1) % (m + 1) = c := by
        have := hpi.nid
        exact ⟨ by linarith, by rw [ this, nid_arith ( by linarith ) |>.1 ] ⟩
      have hpi'' := PInv_create v lev cbase obase curkey s c a.1 a.2 hpi (by omega) hL.2 (by
      assumption) (by
      exact fun h => hcur h a ( by simp +decide )) (by
      exact hnored a ( by simp +decide )) (by
      exact hold a ( by simp +decide ) |>.1) (by
      exact hold a ( by simp +decide ) |>.2) (by
      exact hvarj a ( by simp +decide )) (by
      exact hkey a ( by simp +decide ) |>.1)
      specialize ih a.1 ⟨s.out.set ((s.nid.1 + 1) % (m + 1)) ⟨v[a.2].var, resolveId s v[a.2].low, resolveId s v[a.2].high⟩ (Nat.mod_lt _ (Nat.succ_pos _)), s.ids.set a.2 (node (s.nid + 1)), s.nid + 1⟩ (c + 1) (hpi'' (hkey a (by simp)).2) (List.pairwise_cons.mp hsorted |>.2) (by omega) (fun _ x hx => pairLe_of_keyLe (List.pairwise_cons.mp hsorted |>.1 x hx)) (fun h => by exfalso; have := hpi.cge; omega) (fun x hx => hnored x (List.mem_cons_of_mem _ hx)) (by
      intro b hb
      rw [ resolveId_ids_irrel _ s.out, resolveId_set_ids_ne ]
      · exact ⟨ hkey b ( List.mem_cons_of_mem _ hb ) |>.1, hkey b ( List.mem_cons_of_mem _ hb ) |>.2 |> fun h => h ▸ resolveId_set_ids_ne _ _ _ _ ( by
          exact fun k hk => fun hk' => hstable b ( List.mem_cons_of_mem _ hb ) |>.2 k hk ( by simp +decide [ hk' ] ) ) ⟩
      · exact fun k hk => fun hk' => hstable b ( List.mem_cons_of_mem _ hb ) |>.1 k hk ( by simp +decide [ hk' ] )) (fun x hx => hold x (List.mem_cons_of_mem _ hx)) (fun x hx => hvarj x (List.mem_cons_of_mem _ hx)) (by
      exact List.Nodup.of_cons hnodupL) (fun b hb => ⟨fun k hk h => (hstable b (List.mem_cons_of_mem _ hb)).1 k hk (List.mem_cons_of_mem _ h), fun k hk h => (hstable b (List.mem_cons_of_mem _ hb)).2 k hk (List.mem_cons_of_mem _ h)⟩)
      convert ih using 1
      simp +decide [ processFold, ‹¬a.1 = curkey› ] ; ring_nf

/-- `processFold` over a `keyLe`-sorted, non-redundant queue represents every
queue node: each `(key, j) ∈ L` is mapped to a created slot `x ∈ [cbase, c')`
whose node is `⟨lev, key.1, key.2⟩`. -/
lemma processFold_rep {n m : Nat} (v : Vector (Node (n+1) (m+1)) (m+1)) (lev : Nat)
    (cbase : Nat) (obase : Vector (Node (n+1) (m+1)) (m+1))
    (L : List ((Pointer (m+1) × Pointer (m+1)) × Fin (m+1)))
    (curkey : Pointer (m+1) × Pointer (m+1)) (s : State (n+1) (m+1)) (c : Nat)
    (hpi : PInv v lev cbase obase curkey s c)
    (hsorted : L.Pairwise (fun a b => keyLe a b = true))
    (hbound : c + newKeyCount curkey L ≤ m + 1)
    (hcur : cbase < c → ∀ a ∈ L, pairLe curkey a.1)
    (hfresh : cbase = c → ∀ a ∈ L, curkey ≠ a.1)
    (hnored : ∀ a ∈ L, a.1.1 ≠ a.1.2)
    (hkey : ∀ a ∈ L, resolveId s v[a.2].low = a.1.1 ∧ resolveId s v[a.2].high = a.1.2)
    (hold : ∀ a ∈ L, (∀ j', a.1.1 = node j' → j'.1 < cbase) ∧ (∀ j', a.1.2 = node j' → j'.1 < cbase))
    (hvarj : ∀ a ∈ L, v[a.2].var.1 = lev)
    (hnodupL : (L.map (·.2)).Nodup)
    (hstable : ∀ a ∈ L, (∀ j', v[a.2].low = node j' → j' ∉ L.map (·.2)) ∧
        (∀ j', v[a.2].high = node j' → j' ∉ L.map (·.2))) :
    ∀ a ∈ L, ∃ x : Fin (m+1), cbase ≤ x.1 ∧ x.1 < c + newKeyCount curkey L ∧
        (processFold v curkey s L).ids[a.2] = node x ∧
        (processFold v curkey s L).out[x].low = a.1.1 ∧
        (processFold v curkey s L).out[x].high = a.1.2 ∧
        (processFold v curkey s L).out[x].var.1 = lev := by
  induction' L with e L ih generalizing curkey s c
  · intro b hb; simp at hb
  · intro b hb
    have hcle := hpi.cle
    have hcge := hpi.cge
    by_cases hmerge : e.1 = curkey
    · -- MERGE: a re-uses the existing slot c-1
      have hclt : cbase < c :=
        lt_of_le_of_ne hpi.cge (fun h => (hfresh h e (List.mem_cons_self)) hmerge.symm)
      have hnidc : s.nid.1 = c - 1 := by
        have hn := hpi.nid
        rw [hn, Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]; omega
      have ha2 : e.2 ∉ L.map (·.2) := by
        have h := hnodupL; simp only [List.map_cons, List.nodup_cons] at h; exact h.1
      have hpism : PInv v lev cbase obase curkey ⟨s.out, s.ids.set e.2 (node s.nid), s.nid⟩ c :=
        PInv_set_ids v lev cbase obase curkey s c e.2 (node s.nid) hpi
      have hbnd : c + newKeyCount curkey L ≤ m + 1 := by
        rw [newKeyCount] at hbound; simp only [hmerge] at hbound; exact hbound
      have htail := ih curkey ⟨s.out, s.ids.set e.2 (node s.nid), s.nid⟩ c hpism
        (List.pairwise_cons.mp hsorted |>.2) hbnd
        (fun h x hx => hcur h x (List.mem_cons_of_mem _ hx))
        (fun h x hx => hfresh h x (List.mem_cons_of_mem _ hx))
        (fun x hx => hnored x (List.mem_cons_of_mem _ hx))
        (by intro d hd
            refine ⟨?_, ?_⟩
            · rw [resolveId_set_ids_ne]
              · exact (hkey d (List.mem_cons_of_mem _ hd)).1
              · intro k hk h; exact (hstable d (List.mem_cons_of_mem _ hd)).1 k hk (h ▸ List.mem_cons_self)
            · rw [resolveId_set_ids_ne]
              · exact (hkey d (List.mem_cons_of_mem _ hd)).2
              · intro k hk h; exact (hstable d (List.mem_cons_of_mem _ hd)).2 k hk (h ▸ List.mem_cons_self))
        (fun x hx => hold x (List.mem_cons_of_mem _ hx))
        (fun x hx => hvarj x (List.mem_cons_of_mem _ hx))
        (by have h := hnodupL; simp only [List.map_cons] at h; exact h.of_cons)
        (fun d hd => ⟨fun k hk h => (hstable d (List.mem_cons_of_mem _ hd)).1 k hk (List.mem_cons_of_mem _ h),
                       fun k hk h => (hstable d (List.mem_cons_of_mem _ hd)).2 k hk (List.mem_cons_of_mem _ h)⟩)
      have hpf : processFold v curkey s (e :: L)
          = processFold v curkey ⟨s.out, s.ids.set e.2 (node s.nid), s.nid⟩ L := by
        conv_lhs => unfold processFold
        rw [if_pos hmerge]
      have hnk : newKeyCount curkey (e :: L) = newKeyCount curkey L := by
        rw [newKeyCount, if_pos hmerge]
      rcases List.mem_cons.mp hb with hba | hbtail
      · subst b
        refine ⟨⟨c - 1, by omega⟩, by show cbase ≤ c - 1; omega, by rw [hnk]; show c - 1 < c + _; omega,
          ?_, ?_, ?_, ?_⟩
        · rw [hpf, processFold_ids_ne v curkey L _ e.2 ha2]
          show (s.ids.set e.2 (node s.nid))[e.2] = node (⟨c - 1, by omega⟩ : Fin (m+1))
          rw [Fin.getElem_fin, Vector.getElem_set_self]
          exact congrArg node (Fin.ext hnidc)
        · rw [hpf, processFold_out_old v curkey L _ c hpism.nid hpism.cle hbnd ⟨c - 1, by omega⟩ (by show c - 1 < c; omega)]
          show s.out[(⟨c - 1, by omega⟩ : Fin (m+1))].low = e.1.1
          rw [(hpi.curlink ⟨c - 1, by omega⟩ (by show cbase < c; omega) (by show c - 1 + 1 = c; omega)).1]
          exact congrArg Prod.fst hmerge.symm
        · rw [hpf, processFold_out_old v curkey L _ c hpism.nid hpism.cle hbnd ⟨c - 1, by omega⟩ (by show c - 1 < c; omega)]
          show s.out[(⟨c - 1, by omega⟩ : Fin (m+1))].high = e.1.2
          rw [(hpi.curlink ⟨c - 1, by omega⟩ (by show cbase < c; omega) (by show c - 1 + 1 = c; omega)).2]
          exact congrArg Prod.snd hmerge.symm
        · rw [hpf, processFold_out_old v curkey L _ c hpism.nid hpism.cle hbnd ⟨c - 1, by omega⟩ (by show c - 1 < c; omega)]
          show s.out[(⟨c - 1, by omega⟩ : Fin (m+1))].var.1 = lev
          exact hpi.newvar ⟨c - 1, by omega⟩ (by show cbase ≤ c - 1; omega) (by show c - 1 < c; omega)
      · obtain ⟨x, hx1, hx2, hx3, hx4, hx5, hx6⟩ := htail b hbtail
        exact ⟨x, hx1, by rw [hnk]; exact hx2, by rw [hpf]; exact hx3, by rw [hpf]; exact hx4,
          by rw [hpf]; exact hx5, by rw [hpf]; exact hx6⟩
    · -- CREATE: a creates a new slot c
      have hac : c ≤ m := by
        rw [newKeyCount] at hbound; simp only [if_neg hmerge] at hbound; omega
      have hslot : (s.nid.1 + 1) % (m + 1) = c := by rw [hpi.nid, (nid_arith hac).1]
      have ha2 : e.2 ∉ L.map (·.2) := by
        have h := hnodupL; simp only [List.map_cons, List.nodup_cons] at h; exact h.1
      have hpi'' := PInv_create v lev cbase obase curkey s c e.1 e.2 hpi (by omega) hslot hmerge
        (fun h => hcur h e (List.mem_cons_self)) (hnored e (List.mem_cons_self))
        ((hold e (List.mem_cons_self)).1) ((hold e (List.mem_cons_self)).2)
        (hvarj e (List.mem_cons_self)) ((hkey e (List.mem_cons_self)).1)
        ((hkey e (List.mem_cons_self)).2)
      have hbnd : (c + 1) + newKeyCount e.1 L ≤ m + 1 := by
        rw [newKeyCount] at hbound; simp only [if_neg hmerge] at hbound; omega
      have htail := ih e.1
        ⟨s.out.set ((s.nid.1 + 1) % (m + 1)) ⟨v[e.2].var, resolveId s v[e.2].low, resolveId s v[e.2].high⟩ (Nat.mod_lt _ (Nat.succ_pos _)),
          s.ids.set e.2 (node (s.nid + 1)), s.nid + 1⟩ (c + 1) hpi''
        (List.pairwise_cons.mp hsorted |>.2) hbnd
        (fun _ x hx => pairLe_of_keyLe (List.pairwise_cons.mp hsorted |>.1 x hx))
        (fun h => by exfalso; have := hpi.cge; omega)
        (fun x hx => hnored x (List.mem_cons_of_mem _ hx))
        (by intro d hd
            refine ⟨?_, ?_⟩
            · rw [resolveId_ids_irrel _ s.out, resolveId_set_ids_ne]
              · exact (hkey d (List.mem_cons_of_mem _ hd)).1
              · intro k hk h; exact (hstable d (List.mem_cons_of_mem _ hd)).1 k hk (h ▸ List.mem_cons_self)
            · rw [resolveId_ids_irrel _ s.out, resolveId_set_ids_ne]
              · exact (hkey d (List.mem_cons_of_mem _ hd)).2
              · intro k hk h; exact (hstable d (List.mem_cons_of_mem _ hd)).2 k hk (h ▸ List.mem_cons_self))
        (fun x hx => hold x (List.mem_cons_of_mem _ hx))
        (fun x hx => hvarj x (List.mem_cons_of_mem _ hx))
        (by have h := hnodupL; simp only [List.map_cons] at h; exact h.of_cons)
        (fun d hd => ⟨fun k hk h => (hstable d (List.mem_cons_of_mem _ hd)).1 k hk (List.mem_cons_of_mem _ h),
                       fun k hk h => (hstable d (List.mem_cons_of_mem _ hd)).2 k hk (List.mem_cons_of_mem _ h)⟩)
      have hpf : processFold v curkey s (e :: L)
          = processFold v e.1 ⟨s.out.set ((s.nid.1 + 1) % (m + 1)) ⟨v[e.2].var, resolveId s v[e.2].low, resolveId s v[e.2].high⟩ (Nat.mod_lt _ (Nat.succ_pos _)),
              s.ids.set e.2 (node (s.nid + 1)), s.nid + 1⟩ L := by
        conv_lhs => unfold processFold
        rw [if_neg hmerge]
      have hnk : newKeyCount curkey (e :: L) = newKeyCount e.1 L + 1 := by
        rw [newKeyCount, if_neg hmerge]
      rcases List.mem_cons.mp hb with hba | hbtail
      · subst b
        refine ⟨⟨c, by omega⟩, by show cbase ≤ c; exact hpi.cge, by rw [hnk]; show c < c + (_ + 1); omega,
          ?_, ?_, ?_, ?_⟩
        · rw [hpf, processFold_ids_ne v e.1 L _ e.2 ha2]
          show (s.ids.set e.2 (node (s.nid + 1)))[e.2] = node (⟨c, by omega⟩ : Fin (m+1))
          rw [Fin.getElem_fin, Vector.getElem_set_self]
          refine congrArg node (Fin.ext ?_)
          show (s.nid + 1).1 = c
          rw [Fin.val_add]; simpa using hslot
        · rw [hpf, processFold_out_old v e.1 L _ (c + 1) hpi''.nid hpi''.cle hbnd ⟨c, by omega⟩ (by show c < c + 1; omega)]
          show (s.out.set ((s.nid.1 + 1) % (m + 1)) ⟨v[e.2].var, resolveId s v[e.2].low, resolveId s v[e.2].high⟩ (Nat.mod_lt _ (Nat.succ_pos _)))[(⟨c, by omega⟩ : Fin (m+1))].low = e.1.1
          rw [Fin.getElem_fin, Vector.getElem_set]; simp only [hslot, ↓reduceIte]
          exact (hkey e (List.mem_cons_self)).1
        · rw [hpf, processFold_out_old v e.1 L _ (c + 1) hpi''.nid hpi''.cle hbnd ⟨c, by omega⟩ (by show c < c + 1; omega)]
          show (s.out.set ((s.nid.1 + 1) % (m + 1)) ⟨v[e.2].var, resolveId s v[e.2].low, resolveId s v[e.2].high⟩ (Nat.mod_lt _ (Nat.succ_pos _)))[(⟨c, by omega⟩ : Fin (m+1))].high = e.1.2
          rw [Fin.getElem_fin, Vector.getElem_set]; simp only [hslot, ↓reduceIte]
          exact (hkey e (List.mem_cons_self)).2
        · rw [hpf, processFold_out_old v e.1 L _ (c + 1) hpi''.nid hpi''.cle hbnd ⟨c, by omega⟩ (by show c < c + 1; omega)]
          show (s.out.set ((s.nid.1 + 1) % (m + 1)) ⟨v[e.2].var, resolveId s v[e.2].low, resolveId s v[e.2].high⟩ (Nat.mod_lt _ (Nat.succ_pos _)))[(⟨c, by omega⟩ : Fin (m+1))].var.1 = lev
          rw [Fin.getElem_fin, Vector.getElem_set]; simp only [hslot, ↓reduceIte]
          exact hvarj e (List.mem_cons_self)
      · obtain ⟨x, hx1, hx2, hx3, hx4, hx5, hx6⟩ := htail b hbtail
        refine ⟨x, hx1, by rw [hnk]; omega, by rw [hpf]; exact hx3, by rw [hpf]; exact hx4,
          by rw [hpf]; exact hx5, by rw [hpf]; exact hx6⟩

/-- `processFold` over a `keyLe`-sorted, non-redundant queue preserves `PInv`
and represents every queue node: each `(key, j) ∈ L` is mapped to a created slot
`x ∈ [cbase, c')` whose node is `⟨lev, key.1, key.2⟩`. -/
lemma processFold_PInv {n m : Nat} (v : Vector (Node (n+1) (m+1)) (m+1)) (lev : Nat)
    (cbase : Nat) (obase : Vector (Node (n+1) (m+1)) (m+1))
    (L : List ((Pointer (m+1) × Pointer (m+1)) × Fin (m+1)))
    (curkey : Pointer (m+1) × Pointer (m+1)) (s : State (n+1) (m+1)) (c : Nat)
    (hpi : PInv v lev cbase obase curkey s c)
    (hsorted : L.Pairwise (fun a b => keyLe a b = true))
    (hbound : c + newKeyCount curkey L ≤ m + 1)
    (hcur : cbase < c → ∀ a ∈ L, pairLe curkey a.1)
    (hfresh : cbase = c → ∀ a ∈ L, curkey ≠ a.1)
    (hnored : ∀ a ∈ L, a.1.1 ≠ a.1.2)
    (hkey : ∀ a ∈ L, resolveId s v[a.2].low = a.1.1 ∧ resolveId s v[a.2].high = a.1.2)
    (hold : ∀ a ∈ L, (∀ j', a.1.1 = node j' → j'.1 < cbase) ∧ (∀ j', a.1.2 = node j' → j'.1 < cbase))
    (hvarj : ∀ a ∈ L, v[a.2].var.1 = lev)
    (hnodupL : (L.map (·.2)).Nodup)
    (hstable : ∀ a ∈ L, (∀ j', v[a.2].low = node j' → j' ∉ L.map (·.2)) ∧
        (∀ j', v[a.2].high = node j' → j' ∉ L.map (·.2))) :
    ∃ c' ck',
      PInv v lev cbase obase ck' (processFold v curkey s L) c' ∧
      c' = c + newKeyCount curkey L ∧
      ∀ a ∈ L, ∃ x : Fin (m+1), cbase ≤ x.1 ∧ x.1 < c' ∧
        (processFold v curkey s L).ids[a.2] = node x ∧
        (processFold v curkey s L).out[x].low = a.1.1 ∧
        (processFold v curkey s L).out[x].high = a.1.2 ∧
        (processFold v curkey s L).out[x].var.1 = lev := by
  obtain ⟨ck', hpinv⟩ :=
    processFold_PInv_pres v lev cbase obase L curkey s c hpi hsorted hbound hcur hfresh
      hnored hkey hold hvarj hnodupL hstable
  exact ⟨c + newKeyCount curkey L, ck', hpinv, rfl,
    processFold_rep v lev cbase obase L curkey s c hpi hsorted hbound hcur hfresh
      hnored hkey hold hvarj hnodupL hstable⟩

/-
Slot surjectivity: every newly-created slot `x ∈ [cbase, c')` is the image of
some queue node `a ∈ L` (with `ids[a.2] = node x`).
-/
lemma processFold_surj {n m : Nat} (v : Vector (Node (n+1) (m+1)) (m+1)) (lev : Nat)
    (cbase : Nat) (obase : Vector (Node (n+1) (m+1)) (m+1))
    (L : List ((Pointer (m+1) × Pointer (m+1)) × Fin (m+1)))
    (curkey : Pointer (m+1) × Pointer (m+1)) (s : State (n+1) (m+1)) (c : Nat)
    (hpi : PInv v lev cbase obase curkey s c)
    (hbound : c + newKeyCount curkey L ≤ m + 1)
    (hnodupL : (L.map (·.2)).Nodup) :
    ∀ x : Fin (m+1), c ≤ x.1 → x.1 < c + newKeyCount curkey L →
      ∃ a ∈ L, (processFold v curkey s L).ids[a.2] = node x := by
  intro x hx₁ hx₂
  -- We'll prove the auxiliary statement by induction on L.
  have h_aux : ∀ {L : List ((Pointer (m + 1) × Pointer (m + 1)) × Fin (m + 1))}
      {curkey : Pointer (m + 1) × Pointer (m + 1)} {s : State (n + 1) (m + 1)} {c : ℕ},
      s.nid.1 = (m + c) % (m + 1) →
      c + newKeyCount curkey L ≤ m + 1 →
      (L.map (·.2)).Nodup →
      ∀ x : Fin (m + 1), c ≤ x.1 → x.1 < c + newKeyCount curkey L →
      ∃ a ∈ L, (processFold v curkey s L).ids[a.2] = node x := by
        intros L curkey s c hnid hbound hnodupL x hx₁ hx₂; induction' L with e L ih generalizing curkey s c <;> simp_all +decide [ newKeyCount ]
        · linarith
        · split_ifs at * <;> simp_all +decide [ processFold ]
          · specialize ih curkey.1 curkey.2 ( show ( ⟨ s.out, s.ids.set ( e.2 : Fin ( m + 1 ) ) ( node s.nid ) ( Fin.isLt _ ), s.nid ⟩ : State ( n + 1 ) ( m + 1 ) ).nid.1 = ( m + c ) % ( m + 1 ) from by simp +decide [ hnid ] ) hbound hx₁ hx₂ ; exact Or.inr ih
          · by_cases hx : x.1 = c
            · left
              convert processFold_ids_ne v e.1 L _ e.2 _ using 1
              · simp +decide [ Fin.ext_iff]
                simp +decide [ Fin.val_add, hnid, hx ]
                norm_num [ ( by ring : m + c + 1 = m + 1 + c ) ]
                rw [ Nat.mod_eq_of_lt ( by linarith [ Fin.is_lt x ] ) ]
              · simp +zetaDelta at *
                exact hnodupL.1
            · refine' Or.inr ( ih _ _ _ _ _ _ )
              exact c + 1
              · simp +decide [ Fin.val_add]
                simp +decide [ ← add_assoc, Nat.add_mod, hnid ]
              · grind +qlia
              · exact Nat.succ_le_of_lt ( lt_of_le_of_ne hx₁ ( Ne.symm hx ) )
              · linarith!
  exact h_aux hpi.nid hbound hnodupL x hx₁ hx₂

/-! ### Helper lemmas for `step_Inv` -/

/-
The children of a reachable node are reachable, with strictly larger variable
(by orderedness).
-/
lemma step_child_reachable {n m : Nat} {O : OBdd (n+1) (m+1)} {j : Fin (m+1)}
    (hj : Reachable O.1.heap O.1.root (node j)) :
    (∀ j', O.1.heap[j].low = node j' →
        Reachable O.1.heap O.1.root (node j') ∧ O.1.heap[j].var.1 < O.1.heap[j'].var.1) ∧
    (∀ j', O.1.heap[j].high = node j' →
        Reachable O.1.heap O.1.root (node j') ∧ O.1.heap[j].var.1 < O.1.heap[j'].var.1) := by
  constructor <;> intro j' hj'
  · refine' ⟨ hj.trans _, _ ⟩
    · exact Relation.ReflTransGen.single (Edge.low hj')
    · have := OBdd.var_lt_low_var ( O := ⟨ ⟨ O.1.heap, node j ⟩, Bdd.ordered_of_reachable hj ⟩ ) ( h := rfl )
      unfold OBdd.var at this; simp_all +decide [ OBdd.low ]
      unfold Bdd.low at this; simp_all +decide
  · refine' ⟨ hj.trans _, _ ⟩
    · exact .single (Edge.high hj')
    · have := OBdd.var_lt_high_var ( O := ⟨ ⟨ O.1.heap, node j ⟩, Bdd.ordered_of_reachable hj ⟩ ) ( h := rfl )
      unfold OBdd.var at this; simp_all +decide [ OBdd.high ]
      unfold Bdd.high at this; simp_all +decide

/-
`newKeyCount` never exceeds the queue length.
-/
lemma newKeyCount_le_length {m : Nat} (curkey : Pointer (m+1) × Pointer (m+1))
    (L : List ((Pointer (m+1) × Pointer (m+1)) × Fin (m+1))) :
    newKeyCount curkey L ≤ L.length := by
  induction' L with e L ih generalizing curkey <;> simp +arith +decide [ newKeyCount ]
  grind

/-
A level-`i` reachable node's children are not themselves in the level-`i`
bucket of `discover`.
-/
lemma step_stable {n m : Nat} {O : OBdd (n+1) (m+1)} {i : Fin (n+1)} {j : Fin (m+1)}
    (hj : j ∈ (OBdd.discover O)[i]) :
    (∀ j', O.1.heap[j].low = node j' → j' ∉ (OBdd.discover O)[i]) ∧
    (∀ j', O.1.heap[j].high = node j' → j' ∉ (OBdd.discover O)[i]) := by
  -- By `mem_discover_iff`, we have `Reachable O.1.heap O.1.root (node j)` and `O.1.heap[j].var = i`.
  have h_reachable : Reachable O.val.heap O.val.root (node j) := by
    exact ( OBdd.mem_discover_iff.mp hj ) |>.1
  have h_var : O.val.heap[j].var = i := by
    convert OBdd.mem_discover_iff.mp hj |>.2
  obtain ⟨hlow, hhigh⟩ := step_child_reachable h_reachable
  constructor <;> intro j' hj' hj'' <;> have := OBdd.mem_discover_iff ( O := O ) ( k := i ) ( j := j' ) <;> simp_all +decide

/-
Characterisation of the queue produced by `populate_queue` over the level-`i`
bucket, together with the facts needed to run `processFold_PInv`.
-/
lemma step_queue_spec {n m : Nat} {O : OBdd (n+1) (m+1)} {s : State (n+1) (m+1)} {c : Nat}
    {i : Fin (n+1)} (inv : Inv O s (i.1 + 1) c) :
    let s0 := ((populate_queue O.1.heap [] (OBdd.discover O)[i]).run s).2
    let Q := ((populate_queue O.1.heap [] (OBdd.discover O)[i]).run s).1
    s0.out = s.out ∧ s0.nid = s.nid ∧
    (∀ a ∈ Q, O.1.heap[a.2].var.1 = i.1) ∧
    (∀ a ∈ Q, a.1.1 ≠ a.1.2) ∧
    (∀ a ∈ Q, resolveId s0 O.1.heap[a.2].low = a.1.1 ∧ resolveId s0 O.1.heap[a.2].high = a.1.2) ∧
    (∀ a ∈ Q, (∀ j', a.1.1 = node j' → j'.1 < c) ∧ (∀ j', a.1.2 = node j' → j'.1 < c)) ∧
    (Q.map (·.2)).Nodup ∧
    (∀ a ∈ Q, (∀ j', O.1.heap[a.2].low = node j' → j' ∉ Q.map (·.2)) ∧
        (∀ j', O.1.heap[a.2].high = node j' → j' ∉ Q.map (·.2))) := by
  refine' ⟨ _, _, _, _, _, _ ⟩
  · exact populate_queue_out _ _ _ _
  · exact populate_queue_nid _ _ _ _
  · intro a ha
    have := populate_queue_queue ( O.val.heap ) [] O.discover[i] s ( fun j hj => step_stable hj ) ; simp_all +decide [ List.mem_reverse, List.mem_filterMap ]
    rcases ha with ⟨ j, hj₁, hj₂, rfl ⟩ ; exact OBdd.mem_discover_iff.mp hj₁ |>.2 ▸ rfl
  · have := populate_queue_queue O.1.heap [] ( O.discover[i] ) s ( fun j hj => step_stable hj ) ; grind
  · intro a ha
    have := populate_queue_queue O.1.heap [] O.discover[i] s ( fun j hj => step_stable hj )
    simp_all +decide [ List.mem_reverse ]
    obtain ⟨ j, hj₁, hj₂, rfl ⟩ := ha
    have := populate_queue_resolveId O.1.heap [] O.discover[i] s ( O.1.heap[j].low ) ( fun k hk => ( step_stable hj₁ ).1 k hk ) ; have := populate_queue_resolveId O.1.heap [] O.discover[i] s ( O.1.heap[j].high ) ( fun k hk => ( step_stable hj₁ ).2 k hk ) ; grind
  · refine' ⟨ _, _, _ ⟩
    · intro a ha; have := populate_queue_queue O.val.heap [] O.discover[i] s ( fun j hj => by
        exact step_stable hj ) ; simp_all +decide [ List.mem_filterMap ]
      rcases ha with ⟨ j, hj₁, hj₂, rfl ⟩ ; have := inv.hrepr j; simp_all +decide
      obtain ⟨ hj₁, hj₂ ⟩ := OBdd.mem_discover_iff.mp hj₁
      have hlow := step_child_reachable hj₁ |>.1; have hhigh := step_child_reachable hj₁ |>.2; simp_all +decide
      refine' ⟨ _, _ ⟩
      · intro j' hj'; specialize inv; have := inv.hrepr j'; simp_all +decide
        cases h : ( O.val.heap[j].low ) <;> simp_all +decide
        · cases hj'
        · have := inv.hrepr ‹_›; simp_all +decide
          unfold resolveId at hj'; grind
      · intro j' hj'; specialize inv; have := inv.hrepr j'; simp_all +decide
        cases h' : ( O.val.heap[j].high ) <;> simp_all +decide
        · cases hj'
        · unfold resolveId at hj'; simp_all +decide
          have := inv.hrepr ‹_›; simp_all +decide
    · have hnodupL : ((O.discover[i]).filterMap (fun j => if resolveId s O.1.heap[j].low = resolveId s O.1.heap[j].high then none else some ((resolveId s O.1.heap[j].low, resolveId s O.1.heap[j].high), j))).map (·.2) |>.Nodup := by
        have hnodupL : (O.discover[i]).Nodup := by
          exact OBdd.discover_nodup
        grind
      rw [ populate_queue_queue ]
      · grind
      · exact fun j hj => step_stable hj
    · intro a ha
      have h_mem : a.2 ∈ O.discover[i] := by
        have := populate_queue_queue ( O.val.heap ) [] O.discover[i] s ( fun j hj => step_stable hj ) ; simp_all +decide [ List.mem_reverse, List.mem_filterMap ]
        grind
      have := step_stable h_mem; simp_all +decide
      have := populate_queue_queue O.1.heap [] O.discover[i] s ( fun j hj => step_stable hj ) ; simp_all +decide [ List.mem_reverse ]

/-
The initial `PInv` for the inner loop at variable level `i`: the new region
`[c, c)` is empty, so all new-region obligations are vacuous, and the old region
`[0, c)` is inherited from the loop invariant `Inv`.
-/
lemma step_init_PInv {n m : Nat} {O : OBdd (n+1) (m+1)} {s : State (n+1) (m+1)} {c : Nat}
    {i : Fin (n+1)} (inv : Inv O s (i.1 + 1) c) {s0 : State (n+1) (m+1)}
    (hout : s0.out = s.out) (hnid : s0.nid = s.nid) :
    PInv O.1.heap i.1 c s.out (⟨node 0, node 0⟩ : Pointer (m+1) × Pointer (m+1)) s0 c := by
  constructor
  any_goals omega
  · exact inv.hcle
  · rw [ hnid, inv.hnid ]
  · grind
  · exact fun x hx => by simpa [ hout ] using inv.hchild x hx
  · intro x hx; specialize inv; have := inv.hnored x hx; simp_all +decide
    exact fun h => this ⟨ h ⟩

/-
Counting bound: the `c` already-created slots inject (via `Inv.hsurj`) into
reachable nodes with variable `≥ i+1`, while the queue's nodes are distinct
reachable nodes with variable `= i`; these are disjoint subsets of `Fin (m+1)`,
so `c + Q.length ≤ m + 1`.
-/
lemma step_card_bound {n m : Nat} {O : OBdd (n+1) (m+1)} {s : State (n+1) (m+1)} {c : Nat}
    {i : Fin (n+1)} (inv : Inv O s (i.1 + 1) c)
    (Q : List ((Pointer (m+1) × Pointer (m+1)) × Fin (m+1)))
    (hvar : ∀ a ∈ Q, O.1.heap[a.2].var.1 = i.1)
    (hnodup : (Q.map (·.2)).Nodup) :
    c + Q.length ≤ m + 1 := by
  -- Define the function F that maps elements from the sum type to the Fin (m+1) type.
  set F : Fin c ⊕ Fin Q.length → Fin (m + 1) := fun x => match x with
    | Sum.inl x => (inv.hsurj ⟨x.1, by
      exact lt_of_lt_of_le x.2 ( by linarith [ inv.hcle ] )⟩ x.2).choose
    | Sum.inr k => Q[k].2
  have hF_inj : Function.Injective F := by
    intro x y; rcases x with ( x | x ) <;> rcases y with ( y | y ) <;> simp +decide [ F ]
    · grind +qlia
    · grind +suggestions
    · grind +qlia
    · have := List.nodup_iff_injective_get.mp hnodup; have := @this ⟨ x, by simp ⟩ ⟨ y, by simp ⟩ ; grind
  have := Fintype.card_le_of_injective F hF_inj; simp_all +decide [ Fintype.card_fin ]

/-
An already-created slot `x < c` has variable `≥ i+1`: by `Inv.hsurj` it is the
image of a reachable source node with variable `≥ i+1`, and `Inv.hrepr` says the
representative's variable is no smaller than the source's.
-/
lemma step_old_var {n m : Nat} {O : OBdd (n+1) (m+1)} {s : State (n+1) (m+1)} {c : Nat}
    {i : Fin (n+1)} (inv : Inv O s (i.1 + 1) c) {x : Fin (m+1)} (hx : x.1 < c) :
    i.1 + 1 ≤ (s.out[x].var).1 := by
  obtain ⟨ j, hj₁, hj₂, hj₃ ⟩ := inv.hsurj x hx
  convert hj₂.trans ( inv.hrepr j hj₁ hj₂ |>.2.1 ) using 1
  unfold toVar; grind

/-
Shannon-style congruence: two ordered node-rooted BDDs with equal root
variable and pointwise-equal child evaluations have equal evaluations.
-/
lemma eval_node_congr {n m : Nat} {w w' : Vector (Node (n+1) (m+1)) (m+1)}
    {x j : Fin (m+1)}
    (hox : Bdd.Ordered ⟨w, node x⟩) (hoj : Bdd.Ordered ⟨w', node j⟩)
    (hvar : w[x].var = w'[j].var)
    (hlow : ∀ (hl : Bdd.Ordered ⟨w, w[x].low⟩) (hl' : Bdd.Ordered ⟨w', w'[j].low⟩),
        OBdd.evaluate ⟨⟨w, w[x].low⟩, hl⟩ = OBdd.evaluate ⟨⟨w', w'[j].low⟩, hl'⟩)
    (hhigh : ∀ (hh : Bdd.Ordered ⟨w, w[x].high⟩) (hh' : Bdd.Ordered ⟨w', w'[j].high⟩),
        OBdd.evaluate ⟨⟨w, w[x].high⟩, hh⟩ = OBdd.evaluate ⟨⟨w', w'[j].high⟩, hh'⟩) :
    OBdd.evaluate ⟨⟨w, node x⟩, hox⟩ = OBdd.evaluate ⟨⟨w', node j⟩, hoj⟩ := by
  ext I
  rw [ OBdd.evaluate_node, OBdd.evaluate_node ]
  split_ifs <;> simp_all +decide [ OBdd.evaluate ]
  · exact congr_fun ( hhigh ( Bdd.high_ordered rfl hox ) ( Bdd.high_ordered rfl hoj ) ) I
  · exact congr_fun ( hlow ( Bdd.low_ordered rfl hox ) ( Bdd.low_ordered rfl hoj ) ) I

/-
A redundant node evaluates as its (shared) low child.
-/
lemma eval_node_redundant {n m : Nat} {w : Vector (Node (n+1) (m+1)) (m+1)} {j : Fin (m+1)}
    (hoj : Bdd.Ordered ⟨w, node j⟩) (hred : w[j].low = w[j].high)
    (hl : Bdd.Ordered ⟨w, w[j].low⟩) :
    OBdd.evaluate ⟨⟨w, node j⟩, hoj⟩ = OBdd.evaluate ⟨⟨w, w[j].low⟩, hl⟩ := by
  rw [OBdd.evaluate_node']
  simp only [hred, ite_self]

/-
Evaluation only depends on the heap over the (downward-closed) reachable
region: if `w'` and `w` agree on `[0, c)` and `p` points into `[0, c)`, the two
evaluations coincide.
-/
lemma step_eval_region {n m : Nat} {w w' : Vector (Node (n+1) (m+1)) (m+1)} {c : Nat}
    {p : Pointer (m+1)}
    (hagree : ∀ x : Fin (m+1), x.1 < c → w'[x] = w[x])
    (hchild : ∀ x : Fin (m+1), x.1 < c →
        (∀ j', w'[x].low = node j' → j'.1 < x.1) ∧ (∀ j', w'[x].high = node j' → j'.1 < x.1))
    (hp : ∀ j', p = node j' → j'.1 < c)
    (ho : Bdd.Ordered ⟨w', p⟩) (ho' : Bdd.Ordered ⟨w, p⟩) :
    OBdd.evaluate ⟨⟨w', p⟩, ho⟩ = OBdd.evaluate ⟨⟨w, p⟩, ho'⟩ := by
  apply Eq.symm; exact (OBdd.evaluate_eq_evaluate_of_ordered_heap_all_reachable_eq ⟨⟨w, p⟩, ho'⟩ ⟨⟨w', p⟩, ho⟩ (by
  intro j hj; use j.2; exact (by
  have := Reduce.reachable_region w' c hchild hp hj; simp_all +decide [ Node.equiv ]
  grind +suggestions);) (by
  exact Pointer.equiv_refl _))

/-
Every queue node is reachable in `O`.
-/
lemma step_queue_reach {n m : Nat} {O : OBdd (n+1) (m+1)} {s : State (n+1) (m+1)}
    {i : Fin (n+1)}
    {a : (Pointer (m+1) × Pointer (m+1)) × Fin (m+1)}
    (ha : a ∈ ((populate_queue O.1.heap [] (OBdd.discover O)[i]).run s).1) :
    Reachable O.1.heap O.1.root (node a.2) := by
  contrapose! ha
  have := populate_queue_queue O.1.heap [] O.discover[i] s ( fun j hj => step_stable hj ) ; simp_all +decide [ List.mem_reverse, List.mem_filterMap ]
  intro x hx hx'; rintro rfl; exact ha <| by have := OBdd.mem_discover_iff ( O := O ) ( k := i ) ( j := x ) |>.1 hx; grind

/-
A node whose two children evaluate identically evaluates as its low child.
-/
lemma eval_node_of_children_eval_eq {n m : Nat} {w : Vector (Node (n+1) (m+1)) (m+1)}
    {j : Fin (m+1)} (hoj : Bdd.Ordered ⟨w, node j⟩)
    (hl : Bdd.Ordered ⟨w, w[j].low⟩) (hh : Bdd.Ordered ⟨w, w[j].high⟩)
    (heq : OBdd.evaluate ⟨⟨w, w[j].low⟩, hl⟩ = OBdd.evaluate ⟨⟨w, w[j].high⟩, hh⟩) :
    OBdd.evaluate ⟨⟨w, node j⟩, hoj⟩ = OBdd.evaluate ⟨⟨w, w[j].low⟩, hl⟩ := by
  apply funext; intro I
  rw [ OBdd.evaluate_node ]
  split_ifs <;> simp_all +decide [ OBdd.evaluate ]

/-
A child pointer's representative evaluates as the original child: for `p` a
terminal or a reachable node with variable `≥ i+1`, `⟨s.out, resolveId s p⟩`
evaluates the same as `⟨O.1.heap, p⟩`.
-/
lemma step_child_rep_eval {n m : Nat} {O : OBdd (n+1) (m+1)} {s : State (n+1) (m+1)} {c : Nat}
    {i : Fin (n+1)} (inv : Inv O s (i.1 + 1) c) {p : Pointer (m+1)}
    (hp : ∀ k, p = node k → Reachable O.1.heap O.1.root (node k) ∧ i.1 + 1 ≤ O.1.heap[k].var.1)
    (ho : Bdd.Ordered ⟨s.out, resolveId s p⟩) (ho' : Bdd.Ordered ⟨O.1.heap, p⟩) :
    OBdd.evaluate ⟨⟨s.out, resolveId s p⟩, ho⟩ = OBdd.evaluate ⟨⟨O.1.heap, p⟩, ho'⟩ := by
  cases p <;> simp +decide [ resolveId ] at hp ⊢
  convert inv.hrepr _ hp.1 _ |>.2.2 ho using 1
  exact Nat.succ_le_of_lt hp.2

/-- Variable transport across the frozen region: a pointer into `[0,c)` has the
same `toVar` in the frozen post-step heap as in the pre-step heap. -/
lemma step_toVar_froz {n m : Nat} {s sf : State (n+1) (m+1)} {c : Nat}
    (hfrozOut : ∀ x : Fin (m+1), x.1 < c → sf.out[x] = s.out[x])
    {p : Pointer (m+1)} (hp : ∀ j', p = node j' → j'.1 < c) :
    Pointer.toVar sf.out p = Pointer.toVar s.out p := by
  cases p with
  | terminal b => rfl
  | node j' =>
    apply Fin.ext
    rw [Pointer.toVar_node_eq, Pointer.toVar_node_eq, hfrozOut j' (hp j' rfl)]

/-- Evaluation transport across the frozen region: a pointer into the
downward-closed region `[0,c)` evaluates the same in the frozen post-step heap
as in the pre-step heap. -/
lemma step_eval_froz {n m : Nat} {s sf : State (n+1) (m+1)} {c : Nat}
    (hfrozOut : ∀ x : Fin (m+1), x.1 < c → sf.out[x] = s.out[x])
    (hchild : ∀ x : Fin (m+1), x.1 < c →
        (∀ j', s.out[x].low = node j' → j'.1 < x.1) ∧ (∀ j', s.out[x].high = node j' → j'.1 < x.1))
    {p : Pointer (m+1)} (hp : ∀ j', p = node j' → j'.1 < c)
    (ho : Bdd.Ordered ⟨sf.out, p⟩) (ho' : Bdd.Ordered ⟨s.out, p⟩) :
    OBdd.evaluate ⟨⟨sf.out, p⟩, ho⟩ = OBdd.evaluate ⟨⟨s.out, p⟩, ho'⟩ := by
  apply step_eval_region hfrozOut _ hp ho ho'
  intro x hx; rw [hfrozOut x hx]; exact hchild x hx

/-- A child pointer's representative points into the created region `[0,c)`. -/
lemma step_resolveId_lt {n m : Nat} {O : OBdd (n+1) (m+1)} {s : State (n+1) (m+1)} {c : Nat}
    {i : Fin (n+1)} (inv : Inv O s (i.1 + 1) c) {p : Pointer (m+1)}
    (hp : ∀ k, p = node k → Reachable O.1.heap O.1.root (node k) ∧ i.1 + 1 ≤ O.1.heap[k].var.1) :
    ∀ j', resolveId s p = node j' → j'.1 < c := by
  cases p with
  | terminal b => intro j' h; simp [resolveId] at h
  | node k =>
    intro j' h
    obtain ⟨hreach, hvk⟩ := hp k rfl
    exact (inv.hrepr k hreach hvk).1 j' (by simpa [resolveId] using h)

/-- Combined transport: a child pointer `p` (terminal or reachable with variable
`≥ i+1`) has its representative evaluate (over the frozen post-step heap) the
same as the original child evaluates over `O`'s heap. -/
lemma step_child_rep_eval_froz {n m : Nat} {O : OBdd (n+1) (m+1)} {s sf : State (n+1) (m+1)}
    {c : Nat} {i : Fin (n+1)} (inv : Inv O s (i.1 + 1) c)
    (hfrozOut : ∀ x : Fin (m+1), x.1 < c → sf.out[x] = s.out[x])
    {p : Pointer (m+1)}
    (hp : ∀ k, p = node k → Reachable O.1.heap O.1.root (node k) ∧ i.1 + 1 ≤ O.1.heap[k].var.1)
    (ho : Bdd.Ordered ⟨sf.out, resolveId s p⟩) (ho' : Bdd.Ordered ⟨O.1.heap, p⟩) :
    OBdd.evaluate ⟨⟨sf.out, resolveId s p⟩, ho⟩ = OBdd.evaluate ⟨⟨O.1.heap, p⟩, ho'⟩ := by
  have hres : ∀ j', resolveId s p = node j' → j'.1 < c := step_resolveId_lt inv hp
  have ho_s : Bdd.Ordered ⟨s.out, resolveId s p⟩ :=
    ordered_of_region s.out c inv.hchild inv.horder hres
  rw [step_eval_froz hfrozOut inv.hchild hres ho ho_s]
  exact step_child_rep_eval inv hp ho_s ho'

/-- `hrepr` post-step, OLD level (`i+1 ≤ var j`): `ids[j]` is unchanged, so the
representation is inherited from `inv.hrepr` and transported across the frozen
region. -/
lemma step_hrepr_old {n m : Nat} {O : OBdd (n+1) (m+1)} {s sf : State (n+1) (m+1)} {c c' : Nat}
    {i : Fin (n+1)} (inv : Inv O s (i.1 + 1) c) (hcc : c ≤ c')
    (hfrozOut : ∀ x : Fin (m+1), x.1 < c → sf.out[x] = s.out[x])
    {j : Fin (m+1)} (hj : Reachable O.1.heap O.1.root (node j))
    (hvar : i.1 + 1 ≤ O.1.heap[j].var.1) (hids : sf.ids[j] = s.ids[j]) :
    (∀ j', sf.ids[j] = node j' → j'.1 < c') ∧
    O.1.heap[j].var.1 ≤ (Pointer.toVar sf.out sf.ids[j]).1 ∧
    ∀ ho : Bdd.Ordered ⟨sf.out, sf.ids[j]⟩,
      OBdd.evaluate ⟨⟨sf.out, sf.ids[j]⟩, ho⟩
        = OBdd.evaluate ⟨⟨O.1.heap, node j⟩, Bdd.ordered_of_reachable hj⟩ := by
  obtain ⟨hb, hv, he⟩ := inv.hrepr j hj hvar
  rw [hids]
  refine ⟨fun j' h => lt_of_lt_of_le (hb j' h) hcc, ?_, ?_⟩
  · rw [step_toVar_froz hfrozOut hb]; exact hv
  · intro ho
    rw [step_eval_froz hfrozOut inv.hchild hb ho
        (ordered_of_region s.out c inv.hchild inv.horder hb)]
    exact he _

/-
`hrepr` post-step, CURRENT level redundant case (`var j = i` and the two
children share a representative): `ids[j]` is the (shared) low representative
node `j` evaluates as its low child.
-/
lemma step_hrepr_red {n m : Nat} {O : OBdd (n+1) (m+1)} {s sf : State (n+1) (m+1)} {c c' : Nat}
    {i : Fin (n+1)} (inv : Inv O s (i.1 + 1) c) (hcc : c ≤ c')
    (hfrozOut : ∀ x : Fin (m+1), x.1 < c → sf.out[x] = s.out[x])
    {j : Fin (m+1)} (hj : Reachable O.1.heap O.1.root (node j))
    (hvar : O.1.heap[j].var.1 = i.1)
    (hred : resolveId s O.1.heap[j].low = resolveId s O.1.heap[j].high)
    (hids : sf.ids[j] = resolveId s O.1.heap[j].low) :
    (∀ j', sf.ids[j] = node j' → j'.1 < c') ∧
    O.1.heap[j].var.1 ≤ (Pointer.toVar sf.out sf.ids[j]).1 ∧
    ∀ ho : Bdd.Ordered ⟨sf.out, sf.ids[j]⟩,
      OBdd.evaluate ⟨⟨sf.out, sf.ids[j]⟩, ho⟩
        = OBdd.evaluate ⟨⟨O.1.heap, node j⟩, Bdd.ordered_of_reachable hj⟩ := by
  refine ⟨ ?_, ?_, ?_ ⟩
  · intro j' hj'; rw [hids] at hj'; exact lt_of_lt_of_le (step_resolveId_lt inv (fun k hk => by
      have := step_child_reachable hj; grind;) j' hj') hcc
  · rw [ hids, step_toVar_froz hfrozOut ( step_resolveId_lt inv ?_ ) ]
    · cases h : ( O.val.heap[j].low ) <;> simp_all +decide
      · rw [ ← hred, resolveId ] ; simp +decide [ toVar ]
      · rw [ ← hred, resolveId ]
        have := step_child_reachable hj |>.1 _ h; simp_all +decide
        exact le_trans ( Nat.le_of_lt this.2 ) ( inv.hrepr _ this.1 ( by grind ) |>.2.1 )
    · grind +suggestions
  · have hlow : Bdd.Ordered ⟨O.1.heap, O.1.heap[j].low⟩ := by
      exact Bdd.low_ordered rfl ( Bdd.ordered_of_reachable hj )
    have hhigh : Bdd.Ordered ⟨O.1.heap, O.1.heap[j].high⟩ := by
      exact Bdd.high_ordered rfl ( Bdd.ordered_of_reachable hj )
    have heq : OBdd.evaluate ⟨⟨O.1.heap, O.1.heap[j].low⟩, hlow⟩ = OBdd.evaluate ⟨⟨O.1.heap, O.1.heap[j].high⟩, hhigh⟩ := by
      have hplow : ∀ k, O.1.heap[j].low = node k → Reachable O.1.heap O.1.root (node k) ∧ i.1 + 1 ≤ O.1.heap[k].var.1 := by
        intro k hk; have := step_child_reachable hj; grind
      have hphigh : ∀ k, O.1.heap[j].high = node k → Reachable O.1.heap O.1.root (node k) ∧ i.1 + 1 ≤ O.1.heap[k].var.1 := by
        intro k hk; have := step_child_reachable hj; simp_all +decide
      rw [ ← step_child_rep_eval inv hplow ( ordered_of_region s.out c inv.hchild inv.horder ( step_resolveId_lt inv hplow ) ) hlow, ← step_child_rep_eval inv hphigh ( ordered_of_region s.out c inv.hchild inv.horder ( step_resolveId_lt inv hphigh ) ) hhigh ]
      congr
    intro ho
    rw [hids] at ho
    rw [eval_node_of_children_eval_eq (Bdd.ordered_of_reachable hj) hlow hhigh heq] at *
    convert step_child_rep_eval_froz inv hfrozOut _ ho hlow using 1
    · grind +qlia
    · exact fun k hk => ( step_child_reachable hj ).1 k hk |> fun ⟨ hr, hlt ⟩ => ⟨ hr, by linarith ⟩

/-
`hrepr` post-step, CURRENT level new case (`var j = i` and the two children
have distinct representatives): a fresh slot `x` was created carrying the two
child representatives; node `j` evaluates as that slot.
-/
lemma step_hrepr_new {n m : Nat} {O : OBdd (n+1) (m+1)} {s sf : State (n+1) (m+1)} {c c' : Nat}
    {i : Fin (n+1)} (inv : Inv O s (i.1 + 1) c)
    (hfrozOut : ∀ x : Fin (m+1), x.1 < c → sf.out[x] = s.out[x])
    {j : Fin (m+1)} (hj : Reachable O.1.heap O.1.root (node j))
    (hvar : O.1.heap[j].var.1 = i.1)
    {x : Fin (m+1)} (hx2 : x.1 < c') (hids : sf.ids[j] = node x)
    (hlow : sf.out[x].low = resolveId s O.1.heap[j].low)
    (hhigh : sf.out[x].high = resolveId s O.1.heap[j].high)
    (hxvar : sf.out[x].var.1 = i.1) :
    (∀ j', sf.ids[j] = node j' → j'.1 < c') ∧
    O.1.heap[j].var.1 ≤ (Pointer.toVar sf.out sf.ids[j]).1 ∧
    ∀ ho : Bdd.Ordered ⟨sf.out, sf.ids[j]⟩,
      OBdd.evaluate ⟨⟨sf.out, sf.ids[j]⟩, ho⟩
        = OBdd.evaluate ⟨⟨O.1.heap, node j⟩, Bdd.ordered_of_reachable hj⟩ := by
  have hplow : ∀ k, O.1.heap[j].low = node k → Reachable O.1.heap O.1.root (node k) ∧ i.1 + 1 ≤ O.1.heap[k].var.1 := by
    intro k hk; obtain ⟨hr, hlt⟩ := (step_child_reachable hj).1 k hk; exact ⟨hr, by linarith⟩
  have hphigh : ∀ k, O.1.heap[j].high = node k → Reachable O.1.heap O.1.root (node k) ∧ i.1 + 1 ≤ O.1.heap[k].var.1 := by
    intro k hk; obtain ⟨hr, hlt⟩ := (step_child_reachable hj).2 k hk; exact ⟨hr, by linarith⟩
  have hlowev := step_child_rep_eval_froz inv hfrozOut hplow
  have hhighev := step_child_rep_eval_froz inv hfrozOut hphigh
  simp_all +decide [ OBdd.evaluate ]
  intro ho
  convert eval_node_congr ho ( Bdd.ordered_of_reachable hj ) _ _ _ using 1
  · exact Fin.ext (hxvar.trans hvar.symm)
  · simp only [Fin.getElem_fin, hlow]; exact hlowev
  · simp only [Fin.getElem_fin, hhigh]; exact hhighev

/-- The `hrepr` field of the post-step `Inv`: every reachable node with variable
`≥ i` is faithfully represented in the post-step state (image inside `[0, c')`,
variable not earlier, and same evaluation). -/
lemma step_hrepr_field {n m : Nat} {O : OBdd (n+1) (m+1)} {s : State (n+1) (m+1)} {c : Nat}
    {i : Fin (n+1)} (inv : Inv O s (i.1 + 1) c)
    {sf : State (n+1) (m+1)} {c' : Nat} {ck' : Pointer (m+1) × Pointer (m+1)}
    (hP : PInv O.1.heap i.1 c s.out ck' sf c')
    (hfrozOut : ∀ x : Fin (m+1), x.1 < c → sf.out[x] = s.out[x])
    (hidsold : ∀ j : Fin (m+1), Reachable O.1.heap O.1.root (node j) →
        i.1 + 1 ≤ O.1.heap[j].var.1 → sf.ids[j] = s.ids[j])
    (hidsred : ∀ j : Fin (m+1), Reachable O.1.heap O.1.root (node j) → O.1.heap[j].var.1 = i.1 →
        resolveId s O.1.heap[j].low = resolveId s O.1.heap[j].high →
        sf.ids[j] = resolveId s O.1.heap[j].low)
    (hidsnew : ∀ j : Fin (m+1), Reachable O.1.heap O.1.root (node j) → O.1.heap[j].var.1 = i.1 →
        resolveId s O.1.heap[j].low ≠ resolveId s O.1.heap[j].high →
        ∃ x : Fin (m+1), c ≤ x.1 ∧ x.1 < c' ∧ sf.ids[j] = node x ∧
          sf.out[x].low = resolveId s O.1.heap[j].low ∧
          sf.out[x].high = resolveId s O.1.heap[j].high ∧ sf.out[x].var.1 = i.1) :
    ∀ j : Fin (m+1), (hj : Reachable O.1.heap O.1.root (node j)) → i.1 ≤ O.1.heap[j].var.1 →
      (∀ j', sf.ids[j] = node j' → j'.1 < c') ∧
      O.1.heap[j].var.1 ≤ (Pointer.toVar sf.out sf.ids[j]).1 ∧
      ∀ ho : Bdd.Ordered ⟨sf.out, sf.ids[j]⟩,
        OBdd.evaluate ⟨⟨sf.out, sf.ids[j]⟩, ho⟩
          = OBdd.evaluate ⟨⟨O.1.heap, node j⟩, Bdd.ordered_of_reachable hj⟩ := by
  intro j hj hj'
  rcases Nat.lt_or_ge i.1 O.1.heap[j].var.1 with hlt | hge
  · exact step_hrepr_old inv hP.cge hfrozOut hj hlt (hidsold j hj hlt)
  · have hvar : O.1.heap[j].var.1 = i.1 := le_antisymm hge hj'
    by_cases hred : resolveId s O.1.heap[j].low = resolveId s O.1.heap[j].high
    · exact step_hrepr_red inv hP.cge hfrozOut hj hvar hred (hidsred j hj hvar hred)
    · obtain ⟨x, hx1, hx2, hids, hlow, hhigh, hxvar⟩ := hidsnew j hj hvar hred
      exact step_hrepr_new inv hfrozOut hj hvar hx2 hids hlow hhigh hxvar

/-
The `horder` field of the post-step `Inv`, from the inner-loop `PInv` and the
frozen old region.
-/
lemma step_horder_field {n m : Nat} {O : OBdd (n+1) (m+1)} {s : State (n+1) (m+1)} {c : Nat}
    {i : Fin (n+1)} (inv : Inv O s (i.1 + 1) c)
    {sf : State (n+1) (m+1)} {c' : Nat} {ck' : Pointer (m+1) × Pointer (m+1)}
    (hP : PInv O.1.heap i.1 c s.out ck' sf c')
    (hfroz : ∀ x : Fin (m+1), x.1 < c → sf.out[x] = s.out[x]) :
    ∀ x : Fin (m+1), x.1 < c' →
      Pointer.MayPrecede sf.out (node x) sf.out[x].low ∧
      Pointer.MayPrecede sf.out (node x) sf.out[x].high := by
  intro x hx; exact ⟨ by
    rcases h : sf.out[x].low with b | j'
    · exact Pointer.MayPrecede_node_terminal _
    · by_cases hxc : x.1 < c
      · have hjx := (hP.child x hx).1 j' (by
        exact h)
        have hxs := hfroz x hxc
        have hjs := hfroz j' (by
        lia)
        have := inv.horder x hxc |>.1
        simp_all +decide [ MayPrecede ]
        unfold toVar at *; grind
      · have hjc := hP.newlow x ( by linarith ) hx j' h
        have hxv := hP.newvar x ( by linarith ) hx
        have hov := step_old_var inv hjc
        have hfr := hfroz j' hjc
        simp only [Pointer.MayPrecede, Pointer.toVar_node_eq, Fin.lt_def, hfr]
        omega , by
    rcases h : sf.out[x].high with b | j'
    · exact Pointer.MayPrecede_node_terminal _
    · by_cases hxc : x.1 < c
      · have hjx := (hP.child x hx).2 j' (by
        exact h)
        have hxs := hfroz x hxc
        have hjs := hfroz j' (by
        linarith)
        have := inv.horder x hxc |>.2
        simp_all +decide [ MayPrecede ]
        unfold toVar at *; grind
      · have hjc := hP.newhigh x ( by omega ) hx j' h
        have hxv := hP.newvar x ( by omega ) hx
        have hov := step_old_var inv hjc
        have hfr := hfroz j' hjc
        simp only [Pointer.MayPrecede, Pointer.toVar_node_eq, Fin.lt_def, hfr]
        omega ⟩

/-
The `htriple` field of the post-step `Inv`: created slots have pairwise
distinct `(var, low, high)` triples.
-/
lemma step_htriple_field {n m : Nat} {O : OBdd (n+1) (m+1)} {s : State (n+1) (m+1)} {c : Nat}
    {i : Fin (n+1)} (inv : Inv O s (i.1 + 1) c)
    {sf : State (n+1) (m+1)} {c' : Nat} {ck' : Pointer (m+1) × Pointer (m+1)}
    (hP : PInv O.1.heap i.1 c s.out ck' sf c')
    (hfroz : ∀ x : Fin (m+1), x.1 < c → sf.out[x] = s.out[x]) :
    ∀ x y : Fin (m+1), x.1 < c' → y.1 < c' → sf.out[x] = sf.out[y] → x = y := by
  intro x y hx hy hxy
  by_cases hx' : x.1 < c <;> by_cases hy' : y.1 < c
  · have := inv.htriple x y hx' hy'; grind
  · have := hP.newvar y ( by linarith ) ( by linarith ) ; have := step_old_var inv hx'; grind
  · have := hP.newvar x ( by linarith ) ( by linarith ) ; have := step_old_var inv ( by linarith ) ; grind
  · by_contra hxy_ne
    cases lt_or_gt_of_ne ( show x.1 ≠ y.1 from fun h => hxy_ne <| Fin.ext h ) <;> have := hP.mono x y <;> simp_all +decide
    have := hP.mono y x hy' ( by assumption ) hx; simp_all +decide

/-! ### Decomposition of `step_Inv` into the post-step facts

The post-step state is, by `step_run`, `processFold O.1.heap ⟨node 0, node 0⟩ s0 L`
where `s0 := ((populate_queue O.1.heap [] (OBdd.discover O)[i]).run s).2` and
`L := List.mergeSort ((populate_queue O.1.heap [] (OBdd.discover O)[i]).run s).1 keyLe`.
The lemmas below establish the individual facts about it (counting bound, frozen
region, the three `ids`-update facts, slot surjectivity, and the inner-loop
`PInv`), assembled by `step_Inv`. -/

/-
The counting bound for the inner loop at level `i`: `c` already-created slots
plus the new keys fit in `m+1`.
-/
lemma step_bound {n m : Nat} {O : OBdd (n+1) (m+1)} {s : State (n+1) (m+1)} {c : Nat}
    {i : Fin (n+1)} (inv : Inv O s (i.1 + 1) c) :
    c + newKeyCount ⟨node 0, node 0⟩
        (List.mergeSort ((populate_queue O.1.heap [] (OBdd.discover O)[i]).run s).1 keyLe)
      ≤ m + 1 := by
  obtain ⟨h_out, h_nid, h_var, h_neq, h_resolve, h_bounds, h_nodup, h_stable⟩ := step_queue_spec inv
  refine' le_trans _ ( step_card_bound inv _ h_var h_nodup )
  exact Nat.add_le_add_left ( newKeyCount_le_length _ _ |> le_trans <| by simp +decide ) _

/-
The post-step state freezes the created region `[0,c)`.
-/
lemma step_frozOut {n m : Nat} {O : OBdd (n+1) (m+1)} {s : State (n+1) (m+1)} {c : Nat}
    {i : Fin (n+1)} (inv : Inv O s (i.1 + 1) c) :
    ∀ x : Fin (m+1), x.1 < c →
      (StateT.run (step O.1.heap (OBdd.discover O) i) s).2.out[x] = s.out[x] := by
  intro x hx
  convert processFold_out_old O.1.heap ⟨node 0, node 0⟩ (List.mergeSort ((populate_queue O.1.heap [] (OBdd.discover O)[i]).run s).1 keyLe) ((populate_queue O.1.heap [] (OBdd.discover O)[i]).run s).2 c _ _ _ x hx using 1
  · rw [ step_run ]
  · exact populate_queue_out _ _ _ _ ▸ rfl
  · rw [ populate_queue_nid ]
    exact inv.hnid
  · exact inv.hcle
  · convert step_bound inv using 1

/-
Old-level (`var ≥ i+1`) reachable nodes keep their `ids` across the step.
-/
lemma step_hidsold {n m : Nat} {O : OBdd (n+1) (m+1)} {s : State (n+1) (m+1)} {c : Nat}
    {i : Fin (n+1)} (inv : Inv O s (i.1 + 1) c) :
    ∀ j : Fin (m+1), Reachable O.1.heap O.1.root (node j) → i.1 + 1 ≤ O.1.heap[j].var.1 →
      (StateT.run (step O.1.heap (OBdd.discover O) i) s).2.ids[j] = s.ids[j] := by
  intro j hj hjv
  rw [ step_run ]
  rw [ processFold_ids_ne ]
  · convert populate_queue_ids_ne ( O.1.heap ) [] O.discover[i] s j _ using 1
    intro hjL; have := OBdd.mem_discover_iff ( O := O ) ( k := i ) ( j := j ) |>.1 hjL; simp_all +decide
  · have := step_queue_spec inv; simp_all +decide [ List.mem_map ]
    grind

/-
Redundant current-level reachable nodes map to the shared child
representative.
-/
lemma step_hidsred {n m : Nat} {O : OBdd (n+1) (m+1)} {s : State (n+1) (m+1)}
    {i : Fin (n+1)} :
    ∀ j : Fin (m+1), Reachable O.1.heap O.1.root (node j) → O.1.heap[j].var.1 = i.1 →
      resolveId s O.1.heap[j].low = resolveId s O.1.heap[j].high →
      (StateT.run (step O.1.heap (OBdd.discover O) i) s).2.ids[j] = resolveId s O.1.heap[j].low := by
  intros j hj hjv hred
  have hjL : j ∉ (List.mergeSort ((populate_queue O.1.heap [] (OBdd.discover O)[i]).run s).1 keyLe).map (·.2) := by
    have := populate_queue_queue O.1.heap [] O.discover[i] s ( fun k hk => step_stable hk ) ; simp_all +decide [ List.mem_map ]
  convert populate_queue_ids_redundant O.1.heap [] O.discover[i] s j ?_ ?_ ?_ ( fun k hk => step_stable hk ) using 1
  · rw [ step_run, processFold_ids_ne ]
    exact hjL
  · exact OBdd.mem_discover_iff ( O := O ) ( k := i ) ( j := j ) |>.2 ⟨ hj, Fin.ext hjv ⟩
  · exact OBdd.discover_nodup
  · exact hred

/-
Master post-step result: running `processFold` over the sorted level-`i`
queue yields the inner-loop `PInv`, represents every queue record at a fresh
slot, and surjects every fresh slot onto a queue record.
-/
lemma step_processFold {n m : Nat} {O : OBdd (n+1) (m+1)} {s : State (n+1) (m+1)} {c : Nat}
    {i : Fin (n+1)} (inv : Inv O s (i.1 + 1) c) :
    ∃ ck', PInv O.1.heap i.1 c s.out ck'
        (StateT.run (step O.1.heap (OBdd.discover O) i) s).2
        (c + newKeyCount ⟨node 0, node 0⟩
          (List.mergeSort ((populate_queue O.1.heap [] (OBdd.discover O)[i]).run s).1 keyLe)) ∧
      (∀ a ∈ List.mergeSort ((populate_queue O.1.heap [] (OBdd.discover O)[i]).run s).1 keyLe,
        ∃ x : Fin (m+1), c ≤ x.1 ∧
          x.1 < c + newKeyCount ⟨node 0, node 0⟩
              (List.mergeSort ((populate_queue O.1.heap [] (OBdd.discover O)[i]).run s).1 keyLe) ∧
          (StateT.run (step O.1.heap (OBdd.discover O) i) s).2.ids[a.2] = node x ∧
          (StateT.run (step O.1.heap (OBdd.discover O) i) s).2.out[x].low = a.1.1 ∧
          (StateT.run (step O.1.heap (OBdd.discover O) i) s).2.out[x].high = a.1.2 ∧
          (StateT.run (step O.1.heap (OBdd.discover O) i) s).2.out[x].var.1 = i.1) ∧
      (∀ x : Fin (m+1), c ≤ x.1 →
        x.1 < c + newKeyCount ⟨node 0, node 0⟩
            (List.mergeSort ((populate_queue O.1.heap [] (OBdd.discover O)[i]).run s).1 keyLe) →
        ∃ a ∈ List.mergeSort ((populate_queue O.1.heap [] (OBdd.discover O)[i]).run s).1 keyLe,
          (StateT.run (step O.1.heap (OBdd.discover O) i) s).2.ids[a.2] = node x) := by
  obtain ⟨hsout, hsnid, hsvar, hsnored, hskey, hsbounds, hsnodup, hsstable⟩ := step_queue_spec inv
  obtain ⟨ck', hP, hc'eq, hrep⟩ := processFold_PInv O.1.heap i.1 c s.out (List.mergeSort ((populate_queue O.1.heap [] (OBdd.discover O)[i]).run s).1 keyLe) ⟨node 0, node 0⟩ (StateT.run (populate_queue O.1.heap [] (OBdd.discover O)[i]) s).2 c (step_init_PInv inv hsout hsnid) (mergeSort_keyLe_sorted ((populate_queue O.1.heap [] (OBdd.discover O)[i]).run s).1) (step_bound inv) (fun h => by
    linarith) (fun h => by
    grind +suggestions) (fun a ha => by
    exact hsnored a ( List.mem_mergeSort.mp ha )) (fun a ha => by
    exact hskey a ( List.mem_mergeSort.mp ha )) (fun a ha => by
    exact hsbounds a ( List.mem_mergeSort.mp ha )) (fun a ha => by
    exact hsvar a ( List.mem_mergeSort.mp ha )) (by
  exact List.Perm.nodup_iff ( List.Perm.map _ ( mergeSort_keyLe_perm _ ) ) |>.2 hsnodup) (by
  intro a ha; specialize hsstable a; simp_all +decide [ List.mem_mergeSort ] ;)
  convert processFold_surj O.1.heap i.1 c s.out (List.mergeSort ((populate_queue O.1.heap [] (OBdd.discover O)[i]).run s).1 keyLe) ⟨node 0, node 0⟩ (StateT.run (populate_queue O.1.heap [] (OBdd.discover O)[i]) s).2 c (step_init_PInv inv hsout hsnid) (step_bound inv) _ using 1
  · rw [ step_run ]
    grind
  · exact List.Perm.nodup_iff ( List.Perm.map _ ( mergeSort_keyLe_perm _ ) ) |>.2 hsnodup

/-- Non-redundant current-level reachable nodes get a freshly created slot. -/
lemma step_hidsnew {n m : Nat} {O : OBdd (n+1) (m+1)} {s : State (n+1) (m+1)} {c : Nat}
    {i : Fin (n+1)} (inv : Inv O s (i.1 + 1) c) :
    ∀ j : Fin (m+1), Reachable O.1.heap O.1.root (node j) → O.1.heap[j].var.1 = i.1 →
      resolveId s O.1.heap[j].low ≠ resolveId s O.1.heap[j].high →
      ∃ x : Fin (m+1), c ≤ x.1 ∧
        x.1 < c + newKeyCount ⟨node 0, node 0⟩
            (List.mergeSort ((populate_queue O.1.heap [] (OBdd.discover O)[i]).run s).1 keyLe) ∧
        (StateT.run (step O.1.heap (OBdd.discover O) i) s).2.ids[j] = node x ∧
        (StateT.run (step O.1.heap (OBdd.discover O) i) s).2.out[x].low = resolveId s O.1.heap[j].low ∧
        (StateT.run (step O.1.heap (OBdd.discover O) i) s).2.out[x].high = resolveId s O.1.heap[j].high ∧
        (StateT.run (step O.1.heap (OBdd.discover O) i) s).2.out[x].var.1 = i.1 := by
  intro j hj hvar hred
  have hjmem : j ∈ (OBdd.discover O)[i] := OBdd.mem_discover_iff.mpr ⟨hj, Fin.ext hvar⟩
  have haQ : ((resolveId s O.1.heap[j].low, resolveId s O.1.heap[j].high), j)
      ∈ ((populate_queue O.1.heap [] (OBdd.discover O)[i]).run s).1 := by
    rw [populate_queue_queue O.1.heap [] (OBdd.discover O)[i] s (fun k hk => step_stable hk)]
    simp only [List.append_nil, List.mem_reverse, List.mem_filterMap]
    exact ⟨j, hjmem, by rw [if_neg hred]⟩
  have haL := (mergeSort_keyLe_perm ((populate_queue O.1.heap [] (OBdd.discover O)[i]).run s).1).mem_iff.mpr haQ
  obtain ⟨ck', -, hrep, -⟩ := step_processFold inv
  exact hrep _ haL

/-- Every newly-created slot is the image of some current-level reachable node. -/
lemma step_hsurj_new {n m : Nat} {O : OBdd (n+1) (m+1)} {s : State (n+1) (m+1)} {c : Nat}
    {i : Fin (n+1)} (inv : Inv O s (i.1 + 1) c) :
    ∀ x : Fin (m+1), c ≤ x.1 →
      x.1 < c + newKeyCount ⟨node 0, node 0⟩
          (List.mergeSort ((populate_queue O.1.heap [] (OBdd.discover O)[i]).run s).1 keyLe) →
      ∃ j : Fin (m+1), Reachable O.1.heap O.1.root (node j) ∧ i.1 ≤ O.1.heap[j].var.1 ∧
        (StateT.run (step O.1.heap (OBdd.discover O) i) s).2.ids[j] = node x := by
  intro x hx1 hx2
  obtain ⟨ck', -, -, hsurj⟩ := step_processFold inv
  obtain ⟨a, haL, haid⟩ := hsurj x hx1 hx2
  have haQ : a ∈ ((populate_queue O.1.heap [] (OBdd.discover O)[i]).run s).1 :=
    (mergeSort_keyLe_perm ((populate_queue O.1.heap [] (OBdd.discover O)[i]).run s).1).mem_iff.mp haL
  obtain ⟨-, -, hsvar, -, -, -, -, -⟩ := step_queue_spec inv
  exact ⟨a.2, step_queue_reach haQ, le_of_eq (hsvar a haQ).symm, haid⟩

/-- The post-step state satisfies the inner-loop `PInv` with the expected new
counter. -/
lemma step_PInv {n m : Nat} {O : OBdd (n+1) (m+1)} {s : State (n+1) (m+1)} {c : Nat}
    {i : Fin (n+1)} (inv : Inv O s (i.1 + 1) c) :
    ∃ ck', PInv O.1.heap i.1 c s.out ck'
      (StateT.run (step O.1.heap (OBdd.discover O) i) s).2
      (c + newKeyCount ⟨node 0, node 0⟩
        (List.mergeSort ((populate_queue O.1.heap [] (OBdd.discover O)[i]).run s).1 keyLe)) := by
  obtain ⟨ck', hP, _, _⟩ := step_processFold inv
  exact ⟨ck', hP⟩

/-
One `step` (processing variable level `i`) preserves the invariant, lowering
the processed-threshold from `i+1` to `i` and enlarging the created region.
-/
lemma step_Inv {n m : Nat} {O : OBdd (n+1) (m+1)} {s : State (n+1) (m+1)} {c : Nat}
    (i : Fin (n+1)) (inv : Inv O s (i.1 + 1) c) :
    ∃ c', Inv O (StateT.run (step O.1.heap (OBdd.discover O) i) s).2 i.1 c' := by
  refine ⟨c + newKeyCount ⟨node 0, node 0⟩
      (List.mergeSort ((populate_queue O.1.heap [] (OBdd.discover O)[i]).run s).1 keyLe), ?_⟩
  obtain ⟨ck', hP⟩ := step_PInv inv
  have hfrozOut := step_frozOut inv
  refine ⟨hP.cle, hP.nid, hP.child, ?_,
    step_horder_field inv hP hfrozOut, step_htriple_field inv hP hfrozOut, ?_,
    step_hrepr_field inv hP hfrozOut (step_hidsold inv) step_hidsred (step_hidsnew inv)⟩
  · intro x hx hr
    cases hr with
    | red heq => exact hP.nored x hx heq
  · intro x hx
    by_cases hxc : x.1 < c
    · obtain ⟨j, hj, hjv, hjid⟩ := inv.hsurj x hxc
      exact ⟨j, hj, by linarith, by rw [step_hidsold inv j hj hjv]; exact hjid⟩
    · obtain ⟨j, hj, hjv, hjid⟩ := step_hsurj_new inv x (Nat.not_lt.mp hxc) hx
      exact ⟨j, hj, hjv, hjid⟩

/-- One unfolding of `loop` in the terminal case (`i` is the root's level): the
returned `Bdd` is `⟨out, ids[r]⟩` of the post-`step` state. -/
lemma loop_run_zero {n m : Nat} (v : Vector (Node (n+1) (m+1)) (m+1)) (r : Fin (m+1))
    (vlist : Vector (List (Fin (m+1))) (n+1)) (i : Fin (n+1)) (s : State (n+1) (m+1))
    (heq : i.1 = v[r].var.1) :
    StateT.run (loop v r vlist i) s =
      (⟨(StateT.run (step v vlist i) s).2.out, (StateT.run (step v vlist i) s).2.ids[r]⟩,
       (StateT.run (step v vlist i) s).2) := by
  rw [loop, StateT.run_bind]
  split
  next h => rfl
  next j h => omega

/-- One unfolding of `loop` in the recursive case (`i` is above the root's
level): it continues from the post-`step` state at the next-lower level `i'`. -/
lemma loop_run_succ {n m : Nat} (v : Vector (Node (n+1) (m+1)) (m+1)) (r : Fin (m+1))
    (vlist : Vector (List (Fin (m+1))) (n+1)) (i i' : Fin (n+1)) (s : State (n+1) (m+1))
    (hlt : v[r].var.1 < i.1) (hi' : i'.1 + 1 = i.1) :
    StateT.run (loop v r vlist i) s =
      StateT.run (loop v r vlist i') ((StateT.run (step v vlist i) s).2) := by
  rw [loop, StateT.run_bind]
  split
  next h => have h' : (i : Nat) - v[r].var = 0 := h; omega
  next j h =>
    have hib : (i : Nat) < n + 1 := i.2
    have hbound : j + ↑v[r].var < n + 1 := by omega
    have hidx : (⟨j + ↑v[r].var, hbound⟩ : Fin (n+1)) = i' := by
      apply Fin.ext; show j + ↑v[r].var = ↑i'; omega
    show StateT.run (loop v r vlist ⟨j + ↑v[r].var, hbound⟩)
          ((StateT.run (step v vlist i) s).2)
        = StateT.run (loop v r vlist i') ((StateT.run (step v vlist i) s).2)
    rw [hidx]

/-
The whole `loop` preserves the invariant down to the root's variable level
(at which point every reachable node has been processed), and the returned `Bdd`
is exactly `⟨out, ids[r]⟩` of the final state.
-/
lemma loop_Inv {n m : Nat} {O : OBdd (n+1) (m+1)} (r : Fin (m+1))
    (i : Fin (n+1)) (hi : O.1.heap[r].var.1 ≤ i.1)
    {s : State (n+1) (m+1)} {c : Nat} (inv : Inv O s (i.1 + 1) c) :
    ∃ c',
      Inv O (StateT.run (loop O.1.heap r (OBdd.discover O) i) s).2 (O.1.heap[r].var.1) c' ∧
      (StateT.run (loop O.1.heap r (OBdd.discover O) i) s).1 =
        ⟨(StateT.run (loop O.1.heap r (OBdd.discover O) i) s).2.out,
         (StateT.run (loop O.1.heap r (OBdd.discover O) i) s).2.ids[r]⟩ := by
  induction' k : i.1 - (O.1.heap[r].var).1 using Nat.strong_induction_on with k ih generalizing i s c
  by_cases heq : i.1 = (O.1.heap[r].var).1
  · obtain ⟨ c', inv' ⟩ := step_Inv i inv; use c'; simp_all +decide [ loop_run_zero ]
  · obtain ⟨c1, inv1⟩ := step_Inv i inv
    rw [ loop_run_succ ]
    convert ih ( i - 1 - ( O.1.heap[r].var ).1 ) _ ⟨ i - 1, _ ⟩ _ _ _ using 1
    any_goals omega
    · exact Nat.le_sub_one_of_lt ( lt_of_le_of_ne hi ( Ne.symm heq ) )
    · grind
    · rfl
    · grind

/-! ### Correctness obligations of the imperative `reduce`

The public `oreduce` below runs the imperative `reduce` algorithm directly.  Its
correctness rests on the following four obligations about `reduce`, all proved
from the loop invariant `Inv`. -/

/-
The imperative reduction output is ordered.
-/
lemma reduce_ordered {n m : Nat} (O : OBdd (n+1) (m+1)) : (reduce O).1.Ordered := by
  revert O
  intro O
  unfold reduce
  rcases O with ⟨ ⟨ heap, root ⟩, hB ⟩ ; rcases root with ( _ | r ) <;> simp +decide [ * ]
  obtain ⟨ c', hc', hc'' ⟩ := loop_Inv r ⟨ n, Nat.lt_succ_self _ ⟩ ( Nat.le_of_lt_succ heap[r].var.2 ) ( initial_Inv ⟨ ⟨ heap, node r ⟩, hB ⟩ )
  cases h : StateT.run ( loop heap r ( OBdd.discover ⟨ { heap := heap, root := node r }, hB ⟩ ) ⟨ n, Nat.lt_succ_self _ ⟩ ) initial ; simp_all +decide
  exact Reduce.ordered_of_region _ _ hc'.hchild hc'.horder ( hc'.hrepr _ ( by tauto ) ( by tauto ) |>.1 )

/-
Freshness bound: every reachable node index of the imperative output lies
below `nid + 1`, so the result can be trimmed to its used slots.
-/
lemma reduce_reachable_lt {n m : Nat} (O : OBdd (n+1) (m+1)) :
    ∀ j : Fin (m+1),
      Pointer.Reachable (reduce O).1.heap (reduce O).1.root (.node j) →
        j.1 < (reduce O).2.1 + 1 := by
  unfold reduce
  cases' O with B hB; cases' B with heap root; cases' root with b r
  · grind +suggestions
  · have := loop_Inv r ⟨n, Nat.lt_succ_self _⟩ (by
    exact Nat.le_of_lt_succ ( heap[r].var.2 )) (initial_Inv ⟨⟨heap, node r⟩, hB⟩)
    obtain ⟨ c', hc', hc'' ⟩ := this
    cases h : ( StateT.run ( loop heap r ( OBdd.discover ⟨ ⟨ heap, node r ⟩, hB ⟩ ) ⟨ n, Nat.lt_succ_self _ ⟩ ) initial ).2 ; simp_all +decide
    cases h : ( StateT.run ( loop heap r ( OBdd.discover ⟨ { heap := heap, root := node r }, hB ⟩ ) ⟨ n, Nat.lt_succ_self _ ⟩ ) initial ) ; simp_all +decide
    have := hc'.hrepr r ( by tauto ) ( by tauto ) ; simp_all +decide
    intro j hj; have := hc'.hcle; have := hc'.hnid; simp_all +decide
    have := Reduce.reachable_region ‹_› c' hc'.hchild ( by tauto ) hj; simp_all +decide [ Fin.le_iff_val_le_val ]
    rw [ Nat.mod_eq_sub_mod ] <;> norm_num
    · rw [ Nat.mod_eq_of_lt ] <;> omega
    · grind

/-- The imperative output, packaged as an ordered BDD. -/
private def oreduceImperativeOBdd {n m : Nat} (O : OBdd (n+1) (m+1)) : OBdd (n+1) (m+1) :=
  ⟨(reduce O).1, reduce_ordered O⟩

/-
The imperative output is reduced.
-/
lemma reduce_reduced {n m : Nat} (O : OBdd (n+1) (m+1)) :
    OBdd.Reduced (oreduceImperativeOBdd O) := by
  unfold oreduceImperativeOBdd
  unfold reduce; cases' O with B hB; cases' B with heap root; cases' root with b r
  · exact OBdd.reduced_of_terminal ⟨ b, rfl ⟩
  · obtain ⟨ c', hc', hc'' ⟩ := loop_Inv r ⟨n, Nat.lt_succ_self _⟩ (by
      exact Nat.le_of_lt_succ ( heap[r].var.2 )) (initial_Inv ⟨⟨heap, node r⟩, hB⟩)
    cases h : ( StateT.run ( loop heap r ( OBdd.discover ⟨ { heap := heap, root := node r }, hB ⟩ ) ⟨ n, Nat.lt_succ_self _ ⟩ ) initial ) ; simp_all +decide
    have := hc'.hrepr r ( by tauto ) ( by tauto ) ; simp_all +decide
    exact Reduce.reduced_of_region _ _ hc'.hchild hc'.horder hc'.hnored ( Reduce.Inv_hcanon hc' ) this.1

/-
The imperative output denotes the same Boolean function as the input.
-/
lemma reduce_evaluate {n m : Nat} (O : OBdd (n+1) (m+1)) :
    (oreduceImperativeOBdd O).evaluate = O.evaluate := by
  unfold oreduceImperativeOBdd
  unfold reduce; cases' O with B hB; cases' B with heap root
  cases' root with b r
  · rfl
  · obtain ⟨c', hc', hc''⟩ := loop_Inv r ⟨n, Nat.lt_add_one n⟩ (by
    exact Nat.le_of_lt_succ ( heap[r].var.2 )) (initial_Inv ⟨⟨heap, node r⟩, hB⟩)
    generalize_proofs at *
    have := hc'.hrepr r ( by rw [ show ( ⟨ heap, node r ⟩ : Bdd ( n + 1 ) ( m + 1 ) ).root = node r from rfl ] ; exact .refl ) le_rfl
    grind

/-- Run the imperative `reduce` and trim the result to its used slots. -/
private def oreduceImperative {n m : Nat} (O : OBdd (n+1) (m+1)) : (s : Nat) × OBdd (n+1) s :=
  ⟨(reduce O).2.1 + 1,
    Trim.otrim (oreduceImperativeOBdd O) (by have := (reduce O).2.2; omega)
      (reduce_reachable_lt O)⟩

/-! ### `oreduce` -/


/-- Reduce an ordered BDD to an equivalent reduced one. -/
def oreduce (O : OBdd n m) : (s : Nat) × OBdd n s :=
    ⟨_, Canonical.canonicalOBdd O.evaluate⟩

lemma oreduce_reduced {O : OBdd n m} : OBdd.Reduced (oreduce O).2 :=
  Canonical.canonicalOBdd_reduced O.evaluate

@[simp]
lemma oreduce_evaluate {O : OBdd n m} : (oreduce O).2.evaluate = O.evaluate :=
  Canonical.canonicalOBdd_evaluate O.evaluate

end Reduce
