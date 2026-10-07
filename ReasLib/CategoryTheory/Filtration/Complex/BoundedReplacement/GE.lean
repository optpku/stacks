module

public import ReasLib.CategoryTheory.Filtration.Complex.Computation
public import ReasLib.CategoryTheory.Filtration.Complex.Finite
public import ReasLib.CategoryTheory.Filtration.Strict.FiniteKernelCokernel
public import ReasLib.CategoryTheory.Filtration.KernelCokernel.Universal
public import ReasLib.CategoryTheory.Filtration.ZeroObject
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Lower Truncation of Filtered Complexes

This file constructs the filtered analogue of good lower truncation.  At the cutoff it uses the
canonical filtered cokernel, so the object, differential, projection, and descent map are genuine
data.  Finiteness, support, and associated-graded quasi-isomorphism are exposed separately.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory ZeroObject

noncomputable section

universe v u

namespace CategoryTheory.FilteredComplex

open FilteredObject

variable {A : Type u} [Category.{v} A] [Abelian A]

namespace TruncGE

/-- The degree-`n` filtered object in the good lower truncation at `a`. -/
@[stacks 05S5 "filtered lower truncation"]
noncomputable def obj (K : FilteredComplex A) (a n : ℤ) : FilteredObject A :=
  if _ : n < a then 0
  else if _ : n = a then Hom.cokernel (K.d (a - 1) a)
  else K.X n

/-- Below the cutoff, the good lower truncation is zero. -/
@[stacks 05S5 "filtered lower truncation", simp]
theorem obj_eq_zero (K : FilteredComplex A) (a n : ℤ) (hn : n < a) :
    obj K a n = 0 := sorry

/-- At the cutoff, the good lower truncation is the filtered cokernel of the incoming
differential. -/
@[stacks 05S5 "filtered lower truncation", simp]
theorem obj_eq_cokernel (K : FilteredComplex A) (a n : ℤ) (hn : n = a) :
    obj K a n = Hom.cokernel (K.d (a - 1) a) := sorry

/-- Above the cutoff, the good lower truncation retains the original filtered object. -/
@[stacks 05S5 "filtered lower truncation", simp]
theorem obj_eq_self (K : FilteredComplex A) (a n : ℤ) (hn : a < n) :
    obj K a n = K.X n := sorry

/-- A cochain differential starting at the cutoff ends strictly above it. -/
theorem target_gt (a i j : ℤ) (hij : (ComplexShape.up ℤ).Rel i j) (hi : i = a) :
    a < j := sorry

/-- A cochain differential starting above the cutoff also ends above it. -/
theorem target_gt_of_gt (a i j : ℤ) (hij : (ComplexShape.up ℤ).Rel i j) (hi : a < i) :
    a < j := sorry

/-- The incoming cutoff differential composes trivially with every outgoing differential. -/
theorem cutoff_comp (K : FilteredComplex A) (a j : ℤ) :
    K.d (a - 1) a ≫ K.d a j = 0 := sorry

/-- The differential on the good lower truncation. -/
@[stacks 05S5 "filtered lower truncation"]
noncomputable def d (K : FilteredComplex A) (a i j : ℤ) : obj K a i ⟶ obj K a j :=
  if hij : (ComplexShape.up ℤ).Rel i j then
    if hi : i = a then
      eqToHom (obj_eq_cokernel K a i hi) ≫
        Hom.cokernelDesc (K.d (a - 1) a) (K.d a j) (cutoff_comp K a j) ≫
        eqToHom (obj_eq_self K a j (target_gt a i j hij hi)).symm
    else if hai : a < i then
      eqToHom (obj_eq_self K a i hai) ≫ K.d i j ≫
        eqToHom (obj_eq_self K a j (target_gt_of_gt a i j hij hai)).symm
    else 0
  else 0

/-- The lower-truncation differential vanishes away from the cochain shape. -/
theorem shape (K : FilteredComplex A) (a i j : ℤ)
    (hij : ¬ (ComplexShape.up ℤ).Rel i j) : d K a i j = 0 := sorry

/-- Consecutive lower-truncation differentials compose to zero. -/
theorem d_comp_d (K : FilteredComplex A) (a i j k : ℤ)
    (hij : (ComplexShape.up ℤ).Rel i j) (hjk : (ComplexShape.up ℤ).Rel j k) :
    d K a i j ≫ d K a j k = 0 := sorry

end TruncGE

/-- The good lower truncation of a filtered cochain complex. -/
@[stacks 05S5 "filtered lower truncation"]
noncomputable def truncGE (K : FilteredComplex A) (a : ℤ) : FilteredComplex A where
  X := TruncGE.obj K a
  d := TruncGE.d K a
  shape := TruncGE.shape K a
  d_comp_d' := TruncGE.d_comp_d K a

namespace TruncGE

/-- Evaluation of good lower truncation on an object degree. -/
@[stacks 05S5 "filtered lower truncation", simp]
theorem complex_X (K : FilteredComplex A) (a n : ℤ) :
    (truncGE K a).X n = obj K a n := sorry

/-- Evaluation of the good lower-truncation differential. -/
@[stacks 05S5 "filtered lower truncation", simp]
theorem complex_d (K : FilteredComplex A) (a i j : ℤ) :
    (truncGE K a).d i j = d K a i j := sorry

/-- The degreewise component of the canonical projection to good lower truncation. -/
@[stacks 05S5 "filtered lower truncation projection"]
noncomputable def πComponent (K : FilteredComplex A) (a n : ℤ) : K.X n ⟶ obj K a n :=
  if _ : n < a then 0
  else if hna : n = a then
    eqToHom (congrArg (fun m : ℤ ↦ K.X m) hna) ≫ Hom.toCokernel (K.d (a - 1) a) ≫
      eqToHom (obj_eq_cokernel K a n hna).symm
  else if han : a < n then eqToHom (obj_eq_self K a n han).symm
  else 0

/-- The lower-truncation projection commutes with differentials. -/
theorem π_comm (K : FilteredComplex A) (a i j : ℤ) (hij : (ComplexShape.up ℤ).Rel i j) :
    πComponent K a i ≫ d K a i j = K.d i j ≫ πComponent K a j := sorry

end TruncGE

/-- The canonical projection from a filtered complex to its good lower truncation. -/
@[stacks 05S5 "filtered lower truncation projection"]
noncomputable def πTruncGE (K : FilteredComplex A) (a : ℤ) : K ⟶ truncGE K a where
  f := TruncGE.πComponent K a
  comm' := TruncGE.π_comm K a

namespace TruncGE

/-- Evaluation of the canonical lower-truncation projection in one degree. -/
@[stacks 05S5 "filtered lower truncation projection", simp]
theorem π_f (K : FilteredComplex A) (a n : ℤ) :
    (πTruncGE K a).f n = πComponent K a n := sorry

/-- Good lower truncation preserves termwise finite filtrations. -/
@[stacks 05S5 "filtered lower truncation"]
theorem finite (K : FilteredComplex A) (hK : K.HasFiniteFiltrations) (a : ℤ) :
    (truncGE K a).HasFiniteFiltrations := sorry

/-- Good lower truncation is strictly bounded below after forgetting the filtration. -/
@[stacks 05S5 "filtered lower truncation"]
theorem isStrictlyGE (K : FilteredComplex A) (a : ℤ) :
    (truncGE K a).underlying.IsStrictlyGE a := sorry

/-- Good lower truncation preserves a strict upper bound. -/
@[stacks 05S5 "filtered lower truncation"]
theorem isStrictlyLE (K : FilteredComplex A) (a b : ℤ)
    (hK : K.underlying.IsStrictlyLE b) :
    (truncGE K a).underlying.IsStrictlyLE b := sorry

/-- Under lower cohomological boundedness of the associated graded complex, the canonical lower
truncation projection is a filtered quasi-isomorphism. -/
@[stacks 05S5 "filtered lower truncation quasi-isomorphism"]
theorem quasiIso_π (K : FilteredComplex A) (hKfin : K.HasFiniteFiltrations) (a : ℤ)
    (hK : K.associatedGraded.IsGE a) :
    QuasiIso (associatedGradedMap (πTruncGE K a)) := sorry

/-- The incoming differential is killed by any map to a complex strictly bounded below at the
cutoff. -/
theorem incoming_comp {K L : FilteredComplex A} (a : ℤ) (f : K ⟶ L)
    (hL : L.underlying.IsStrictlyGE a) :
    K.d (a - 1) a ≫ f.f a = 0 := sorry

/-- The degreewise component of descent through good lower truncation. -/
@[stacks 05S5 "filtered lower truncation descent"]
noncomputable def descComponent {K L : FilteredComplex A} (a : ℤ) (f : K ⟶ L)
    (hL : L.underlying.IsStrictlyGE a) (n : ℤ) : obj K a n ⟶ L.X n :=
  if _ : n < a then 0
  else if hna : n = a then
    eqToHom (obj_eq_cokernel K a n hna) ≫
      Hom.cokernelDesc (K.d (a - 1) a) (f.f a) (incoming_comp a f hL) ≫
      eqToHom (congrArg (fun m : ℤ ↦ L.X m) hna).symm
  else if han : a < n then eqToHom (obj_eq_self K a n han) ≫ f.f n
  else 0

/-- Descent through good lower truncation commutes with differentials. -/
theorem desc_comm {K L : FilteredComplex A} (a : ℤ) (f : K ⟶ L)
    (hL : L.underlying.IsStrictlyGE a) (i j : ℤ) (hij : (ComplexShape.up ℤ).Rel i j) :
    d K a i j ≫ descComponent a f hL j = descComponent a f hL i ≫ L.d i j := sorry

/-- Any map to a complex strictly bounded below at `a` descends through good lower truncation. -/
@[stacks 05S5 "filtered lower truncation descent"]
noncomputable def desc {K L : FilteredComplex A} (a : ℤ) (f : K ⟶ L)
    (hL : L.underlying.IsStrictlyGE a) : truncGE K a ⟶ L where
  f := descComponent a f hL
  comm' i j hij := (desc_comm a f hL i j hij).symm

/-- Evaluation of lower-truncation descent in one degree. -/
@[stacks 05S5 "filtered lower truncation descent", simp]
theorem desc_f {K L : FilteredComplex A} (a : ℤ) (f : K ⟶ L)
    (hL : L.underlying.IsStrictlyGE a) (n : ℤ) :
    (desc a f hL).f n = descComponent a f hL n := sorry

/-- The lower-truncation projection followed by descent recovers the original map. -/
@[stacks 05S5 "filtered lower truncation descent"]
theorem π_desc {K L : FilteredComplex A} (a : ℤ) (f : K ⟶ L)
    (hL : L.underlying.IsStrictlyGE a) :
    πTruncGE K a ≫ desc a f hL = f := sorry

/-- If `f` and the canonical lower-truncation projection are filtered quasi-isomorphisms, then
the descended map is a filtered quasi-isomorphism as well. -/
@[stacks 05S5 "filtered lower truncation descent"]
theorem quasiIso_desc {K L : FilteredComplex A} (hKfin : K.HasFiniteFiltrations) (a : ℤ)
    (hK : K.associatedGraded.IsGE a) (f : K ⟶ L)
    (hf : QuasiIso (associatedGradedMap f)) (hL : L.underlying.IsStrictlyGE a) :
    QuasiIso (associatedGradedMap (desc a f hL)) := sorry

end TruncGE

end CategoryTheory.FilteredComplex
