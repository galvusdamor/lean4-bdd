import Bdd.Basic
import Mathlib

/-!
# Canonical reduced BDDs

For every Boolean function `g : Vector Bool n → Bool` we construct a reduced
ordered BDD `canonicalOBdd g` that evaluates to `g`.

The heap (for `n = k + 1` inputs) has one slot per Boolean function, addressed by
the truth-table encoding `ttEquiv : (Vector Bool (k+1) → Bool) ≃ Fin (2 ^ 2 ^ (k+1))`.
The slot for an *essential* function `g` (one that depends on some input) holds a
node branching on the least variable `g` depends on, with the two cofactors of
`g` as children.  Slots for non-essential (constant) functions are never reached.

This is a self-contained, computable existence proof of reduced equivalents,
which is all that is needed to discharge the correctness obligations of
`Reduce.oreduce`.
-/

open Pointer Bdd

namespace Canonical

/-- `Vector Bool n` is equivalent to `Fin n → Bool`. -/
def vecEquivFun (n : Nat) : Vector Bool n ≃ (Fin n → Bool) where
  toFun v := fun i ↦ v[i]
  invFun f := Vector.ofFn f
  left_inv := by intro v; ext i hi; simp
  right_inv := by intro f; ext i; simp

instance : Fintype (Vector Bool n) := Fintype.ofEquiv _ (vecEquivFun n).symm

/-- Boolean functions on `n` inputs. -/
abbrev BFun (n : Nat) := Vector Bool n → Bool

instance (g : BFun n) (i : Fin n) : Decidable (Nary.IndependentOf g i) := by
  unfold Nary.IndependentOf; infer_instance

instance (g : BFun n) (i : Fin n) : Decidable (Nary.DependsOn g i) := by
  unfold Nary.DependsOn; infer_instance

instance (g : BFun n) : DecidablePred (Nary.DependsOn g) := fun _ ↦ inferInstance

/-- A function is *essential* if it depends on at least one of its inputs. -/
def Essential (g : BFun n) : Prop := ∃ i, Nary.DependsOn g i

instance : DecidablePred (Essential (n := n)) := fun g ↦ by
  unfold Essential; infer_instance

/-- The least variable an essential function depends on. -/
def topvar (g : BFun n) (h : Essential g) : Fin n :=
  (Finset.univ.filter (Nary.DependsOn g)).min'
    (by obtain ⟨i, hi⟩ := h; exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩⟩)

/-- Termination measure for the recursion on cofactors. -/
def mu (g : BFun n) : Nat := n - (if h : Essential g then (topvar g h).1 else n)

/-! ## General facts about essential functions, independent of the encoding. -/

/-
The least dependent variable is itself a dependent variable.
-/
lemma topvar_dependsOn (g : BFun n) (h : Essential g) : Nary.DependsOn g (topvar g h) := by
  exact Finset.mem_filter.mp ( Finset.min'_mem _ _ ) |>.2

/-
The least dependent variable is `≤` every dependent variable.
-/
lemma topvar_le (g : BFun n) (h : Essential g) {i : Fin n} :
    Nary.DependsOn g i → topvar g h ≤ i := by
  exact fun hi => Finset.min'_le _ _ ( by aesop )

/-
Variables below the least dependent variable are independent.
-/
lemma independentOf_lt_topvar (g : BFun n) (h : Essential g) {i : Fin n} :
    i < topvar g h → Nary.IndependentOf g i := by
  intro hi;
  exact Classical.not_not.1 fun hi' => hi.not_ge <| topvar_le g h <| by simpa [ Nary.DependsOn ] using hi';

/-
Restricting a variable preserves independence of every variable.
-/
lemma independentOf_restrict {g : BFun n} {b : Bool} {i j : Fin n} :
    Nary.IndependentOf g j → Nary.IndependentOf (Nary.restrict g b i) j := by
  intro hg a v;
  convert hg a _ using 1;
  by_cases hij : i = j;
  · simp_all +decide [ Nary.restrict ];
  · convert hg a _ using 1;
    congr 1;
    grind

/-
A function that is not essential is constant.
-/
lemma const_of_not_essential {g : BFun n} (h : ¬ Essential g) (I : Vector Bool n) :
    g I = g (Vector.replicate n false) := by
  -- Since `g` is not essential, for every `i : Fin n`, `Nary.IndependentOf g i`.
  have h_indep : ∀ i : Fin n, Nary.IndependentOf g i := by
    exact fun i => Classical.not_not.1 fun hi => h ⟨ i, by simpa [ Nary.DependsOn ] using hi ⟩;
  apply Nary.eq_of_forall_dependency_getElem_eq;
  exact fun ⟨ i, hi ⟩ => False.elim <| hi <| h_indep i

/-
An essential function is not constant.
-/
lemma not_const_of_essential {g : BFun n} (h : Essential g) (b : Bool) :
    g ≠ Function.const _ b := by
  intro h_const
  obtain ⟨i, hi⟩ := h
  have h_indep : Nary.IndependentOf g i := by
    simp_all +decide [ Nary.IndependentOf ];
  exact hi h_indep

/-
The two cofactors at a dependent variable differ.
-/
lemma restrict_ne_of_dependsOn {g : BFun n} {i : Fin n} :
    Nary.DependsOn g i → Nary.restrict g false i ≠ Nary.restrict g true i := by
  intro h
  by_contra h_contra;
  simp_all +decide [ funext_iff, Nary.restrict ];
  obtain ⟨ x, hx ⟩ := h; specialize h_contra x; simp_all +decide [ Vector.set ] ;
  grind +suggestions

/-
If a cofactor is essential, its least dependent variable is strictly larger.
-/
lemma topvar_lt_restrict {g : BFun n} (h : Essential g) {b : Bool}
    (h' : Essential (Nary.restrict g b (topvar g h))) :
    topvar g h < topvar (Nary.restrict g b (topvar g h)) h' := by
  -- By definition of `topvar`, we know that `topvar g h` is the smallest index `i` such that `Nary.DependsOn g i`.
  have h_topvar_g : ∀ j : Fin n, j ≤ topvar g h → Nary.IndependentOf (Nary.restrict g b (topvar g h)) j := by
    intro j hj;
    by_cases h_cases : j < topvar g h;
    · exact independentOf_restrict ( independentOf_lt_topvar g h h_cases );
    · cases eq_or_lt_of_le hj <;> aesop;
  exact lt_of_not_ge fun h'' => absurd ( h_topvar_g _ h'' ) ( by simpa [ Nary.DependsOn ] using topvar_dependsOn _ h' )

/-
The recursion measure decreases when passing to a cofactor.
-/
lemma mu_restrict_lt {g : BFun n} (h : Essential g) (b : Bool) :
    mu (Nary.restrict g b (topvar g h)) < mu g := by
  by_cases h' : Essential ( Nary.restrict g b ( topvar g h ) ) <;> simp_all +decide [ mu ];
  rw [ tsub_lt_tsub_iff_left_of_le ];
  · convert topvar_lt_restrict h h' using 1;
  · exact Nat.le_of_lt ( Fin.is_lt _ )

/-
Shannon expansion: `g` is recovered from its cofactors at any variable.
-/
lemma shannon (g : BFun n) (i : Fin n) (I : Vector Bool n) :
    g I = if I[i] then Nary.restrict g true i I else Nary.restrict g false i I := by
  split_ifs <;> simp_all +decide [ Nary.restrict ];
  · congr;
    grind;
  · grind +suggestions

/-! ## The canonical heap (for `n = k + 1`). -/

section Succ

variable {k : Nat}

/-- The size of the canonical heap on `k + 1` inputs. -/
def M (k : Nat) : Nat := 2 ^ (2 ^ (k + 1))

/-- Truth-table encoding of Boolean functions as heap indices. -/
def ttEquiv (k : Nat) : BFun (k + 1) ≃ Fin (M k) :=
  (Equiv.arrowCongr
    ((vecEquivFun (k + 1)).trans
      ((Equiv.arrowCongr (Equiv.refl _) finTwoEquiv.symm).trans finFunctionFinEquiv))
    finTwoEquiv.symm).trans finFunctionFinEquiv

/-- The default variable used to fill unreachable slots. -/
def dvar (k : Nat) : Fin (k + 1) := ⟨0, Nat.succ_pos k⟩

/-- The pointer representing the function `g`. -/
def ptr (g : BFun (k + 1)) : Pointer (M k) :=
  if _ : Essential g then Pointer.node (ttEquiv k g)
  else Pointer.terminal (g (Vector.replicate (k + 1) false))

/-- The heap slot for the function `g`. -/
def nodeOf (g : BFun (k + 1)) : Node (k + 1) (M k) :=
  if h : Essential g then
    ⟨topvar g h, ptr (Nary.restrict g false (topvar g h)), ptr (Nary.restrict g true (topvar g h))⟩
  else
    ⟨dvar k, Pointer.terminal (g (Vector.replicate (k + 1) false)),
             Pointer.terminal (g (Vector.replicate (k + 1) false))⟩

/-- The canonical heap on `k + 1` inputs. -/
def cheap (k : Nat) : Vector (Node (k + 1) (M k)) (M k) :=
  Vector.ofFn (fun j ↦ nodeOf ((ttEquiv k).symm j))

@[simp]
lemma cheap_getElem (j : Fin (M k)) : (cheap k)[j.1] = nodeOf ((ttEquiv k).symm j) := by
  grind +locals

/-
The heap slot at the index of an essential function is its node.
-/
lemma cheap_getElem_ttEquiv {g : BFun (k + 1)} :
    (cheap k)[(ttEquiv k g).1] = nodeOf g := by
  grind +suggestions

/-
If `ptr g = node j` then `g` is essential and `j` is its index.
-/
lemma ptr_eq_node {g : BFun (k + 1)} {j : Fin (M k)} :
    ptr g = Pointer.node j → Essential g ∧ j = ttEquiv k g := by
  unfold ptr;
  grind

/-
`ptr` is injective.
-/
lemma ptr_injective {g g' : BFun (k + 1)} : ptr g = ptr g' → g = g' := by
  intro h_eq;
  by_cases h1 : Essential g <;> by_cases h2 : Essential g' <;> simp_all +decide [ ptr ];
  exact funext fun x => by rw [ const_of_not_essential h1 x, const_of_not_essential h2 x, h_eq ] ;

/-
An edge of the canonical heap respects the variable ordering.
-/
lemma cheap_edge_mayPrecede {p q : Pointer (M k)} :
    Edge (cheap k) p q → MayPrecede (cheap k) p q := by
  intro h_edge
  obtain ⟨j, hj⟩ := h_edge;
  · by_cases hj : Essential ((ttEquiv k).symm ‹_›) <;> simp_all +decide [ nodeOf, MayPrecede ];
    · by_cases h : Essential ( Nary.restrict ( ( ttEquiv k ).symm ‹_› ) false ( topvar ( ( ttEquiv k ).symm ‹_› ) hj ) ) <;> simp_all +decide [ ptr, toVar ];
      · convert topvar_lt_restrict hj h using 1; all_goals unfold nodeOf; aesop;
      · grind +suggestions;
    · simp +decide [ toVar, cheap ];
      exact Nat.le_of_lt_succ ( Fin.is_lt _ );
  · rename_i j hj;
    by_cases h : Essential ( ( ttEquiv k ).symm j ) <;> simp_all +decide [ nodeOf ];
    · rw [ ← hj, ptr ];
      split_ifs <;> simp_all +decide [ toVar ];
      · convert topvar_lt_restrict h ‹_› using 1; all_goals unfold nodeOf; aesop;
      · grind +suggestions;
    · subst hj; simp +decide [ toVar ] ;
      grind +suggestions

/-- Every pointer into the canonical heap is the root of an ordered BDD. -/
lemma cheap_ordered (x : Pointer (M k)) : Bdd.Ordered ⟨cheap k, x⟩ := by
  rintro ⟨p, hp⟩ ⟨q, hq⟩ (e : Edge (cheap k) p q)
  exact cheap_edge_mayPrecede e

/-
The sub-BDD rooted at `ptr g` evaluates to `g` (auxiliary, bounded recursion).
-/
lemma ptr_evaluate_aux :
    ∀ (fuel : Nat) (g : BFun (k + 1)), mu g ≤ fuel →
      OBdd.evaluate ⟨⟨cheap k, ptr g⟩, cheap_ordered (ptr g)⟩ = g := by
  intro fuel g hg
  induction' fuel with fuel ih generalizing g;
  · by_cases h : Essential g <;> simp_all +decide [ mu ];
    · exact absurd hg ( Nat.sub_ne_zero_of_lt ( Nat.lt_succ_of_le ( Fin.is_le _ ) ) );
    · unfold ptr; simp +decide [ h ] ;
      exact funext fun x => const_of_not_essential h x ▸ rfl;
  · by_cases h : Essential g <;> simp_all +decide [ ptr ];
    · ext I; simp +decide ;
      split_ifs <;> simp_all +decide [ nodeOf ];
      · convert ih ( Nary.restrict g true ( topvar g h ) ) _ |> congr_fun <| I using 1;
        · convert shannon g ( topvar g h ) I using 1 ; aesop;
        · exact Nat.le_of_lt_succ ( lt_of_lt_of_le ( mu_restrict_lt h true ) hg );
      · convert congr_fun ( ih ( Nary.restrict g false ( topvar g h ) ) ?_ ) I using 1;
        · convert shannon g ( topvar g h ) I using 1 ; aesop;
        · exact Nat.le_of_lt_succ ( mu_restrict_lt h false |> lt_of_lt_of_le <| by linarith );
    · exact funext fun x => const_of_not_essential h x ▸ rfl

/-- The sub-BDD rooted at `ptr g` evaluates to `g`. -/
lemma ptr_evaluate (g : BFun (k + 1)) :
    OBdd.evaluate ⟨⟨cheap k, ptr g⟩, cheap_ordered (ptr g)⟩ = g :=
  ptr_evaluate_aux (mu g) g le_rfl

/-
A node reachable from an essential root is itself essential.
-/
lemma essential_of_reachable {g : BFun (k + 1)} {j : Fin (M k)} :
    Pointer.Reachable (cheap k) (ptr g) (Pointer.node j) → Essential ((ttEquiv k).symm j) := by
  intro hj0
  have h_cofactor : ∀ c : Pointer (M k), Reachable (cheap k) (ptr g) c → ∀ j : Fin (M k), c = node j → Essential ((ttEquiv k).symm j) := by
    intro c hc j hj;
    induction' hc with c hc ih generalizing j;
    · obtain ⟨ _, rfl ⟩ := ptr_eq_node hj; aesop;
    · obtain ⟨ i, hi ⟩ := ‹Edge ( cheap k ) c hc›;
      · grind +locals;
      · grind +locals;
  exact h_cofactor _ hj0 _ rfl

/-
No reachable node of the canonical heap is redundant.
-/
lemma cheap_not_redundant {g : BFun (k + 1)} {j : Fin (M k)}
    (hj : Pointer.Reachable (cheap k) (ptr g) (Pointer.node j)) :
    ¬ Pointer.Redundant (cheap k) (Pointer.node j) := by
  refine' fun h' => _;
  obtain ⟨hj_redundant⟩ := h';
  simp_all +decide [ cheap_getElem, nodeOf ];
  grind +suggestions

/-
The evaluation of a sub-BDD at a reachable pointer determines that pointer.
-/
lemma pointer_of_evaluate {g : BFun (k + 1)} {x y : Pointer (M k)}
    (hx : Pointer.Reachable (cheap k) (ptr g) x) (hy : Pointer.Reachable (cheap k) (ptr g) y)
    (he : OBdd.evaluate ⟨⟨cheap k, x⟩, cheap_ordered x⟩
        = OBdd.evaluate ⟨⟨cheap k, y⟩, cheap_ordered y⟩) : x = y := by
  by_cases hx' : ∃ j, x = .node j <;> by_cases hy' : ∃ j, y = .node j;
  · -- By definition of `ptr`, we know that `ptr ((ttEquiv k).symm j) = .node j` for any `j`.
    have h_ptr_symm : ∀ j : Fin (M k), ptr ((ttEquiv k).symm j) = .node j ∨ ¬Essential ((ttEquiv k).symm j) ∧ ptr ((ttEquiv k).symm j) = .terminal ((ttEquiv k).symm j (Vector.replicate (k + 1) false)) := by
      intro j; by_cases hj : Essential ( ( ttEquiv k ).symm j ) <;> simp +decide [ hj, ptr ] ;
    obtain ⟨ j, rfl ⟩ := hx'
    obtain ⟨ j', rfl ⟩ := hy';
    grind +suggestions;
  · obtain ⟨ j, rfl ⟩ := hx';
    rcases y with ( _ | j ) <;> simp_all +decide [ Reachable ];
    -- By the key computation, the evaluation of the sub-BDD at node j is the function it encodes.
    have h_eval_node : OBdd.evaluate ⟨⟨cheap k, .node j⟩, cheap_ordered _⟩ = (ttEquiv k).symm j := by
      convert ptr_evaluate ( ( ttEquiv k ).symm j ) using 1;
      have := essential_of_reachable hx; simp_all +decide [ ptr ] ;
    have h_not_const : ¬ Essential ((ttEquiv k).symm j) := by
      intro H; have := not_const_of_essential H; aesop;
    exact h_not_const <| essential_of_reachable hx;
  · -- Since x is not a node, it must be a terminal pointer.
    obtain ⟨b, hb⟩ : ∃ b, x = .terminal b := by
      cases x <;> aesop;
    obtain ⟨j, hj⟩ := hy'
    have h_essential : Essential ((ttEquiv k).symm j) := by
      exact essential_of_reachable ( by aesop );
    have h_eval : OBdd.evaluate ⟨⟨cheap k, y⟩, cheap_ordered _⟩ = (ttEquiv k).symm j := by
      convert ptr_evaluate ( ( ttEquiv k ).symm j ) using 1;
      unfold ptr; aesop;
    grind +suggestions;
  · cases x <;> cases y <;> aesop

/-
The canonical BDD rooted at `ptr g` is reduced.
-/
lemma cheap_reduced (g : BFun (k + 1)) : OBdd.Reduced ⟨⟨cheap k, ptr g⟩, cheap_ordered (ptr g)⟩ := by
  constructor;
  · intro p hp;
    by_cases h : Essential g <;> simp_all +decide [ ptr ];
    · obtain ⟨ j, hj ⟩ := p;
      cases j <;> simp_all +decide;
      · cases hp;
      · exact cheap_not_redundant hj hp;
    · cases p ; simp_all +decide;
      cases ‹Pointer ( M k ) › <;> simp_all +decide [ ptr ];
      · cases hp;
      · grind +suggestions;
  · intro p q hpq
    have h_eval : OBdd.evaluate ⟨⟨cheap k, p.1⟩, cheap_ordered p.1⟩ = OBdd.evaluate ⟨⟨cheap k, q.1⟩, cheap_ordered q.1⟩ := by
      convert OBdd.Canonicity_reverse hpq using 1
    have h_ptr : p.1 = q.1 := by
      by_cases h : Essential g <;> simp_all +decide [ OBdd.SimilarRP ];
      · exact pointer_of_evaluate p.2 q.2 h_eval;
      · have h_ptr : ptr g = .terminal (g (Vector.replicate (k + 1) false)) := by
          unfold ptr; aesop;
        grind +suggestions
    exact h_ptr

end Succ

/-! ## The canonical BDD for arbitrary `n`. -/

/-- The size of the canonical heap on `n` inputs. -/
def canonicalSize : Nat → Nat
  | 0 => 0
  | (k + 1) => M k

/-- The canonical reduced ordered BDD representing `g`. -/
def canonicalOBdd : {n : Nat} → (g : BFun n) → OBdd n (canonicalSize n)
  | 0, g => ⟨⟨Vector.emptyWithCapacity 0, .terminal (g (Vector.replicate 0 false))⟩,
             Bdd.Ordered_of_terminal⟩
  | (_ + 1), g => ⟨⟨cheap _, ptr g⟩, cheap_ordered (ptr g)⟩

/-
The canonical BDD for `g` evaluates to `g`.
-/
theorem canonicalOBdd_evaluate {n : Nat} (g : BFun n) : (canonicalOBdd g).evaluate = g := by
  induction' n with k ih;
  · ext I; simp [canonicalOBdd];
    convert rfl;
    exact List.eq_nil_of_length_eq_zero ( by simp +decide );
  · convert ptr_evaluate g using 1

/-
The canonical BDD for `g` is reduced.
-/
theorem canonicalOBdd_reduced {n : Nat} (g : BFun n) : (canonicalOBdd g).Reduced := by
  cases n <;> simp_all +decide [ canonicalOBdd ];
  · exact OBdd.reduced_of_terminal ⟨ _, rfl ⟩;
  · convert cheap_reduced g using 1

end Canonical