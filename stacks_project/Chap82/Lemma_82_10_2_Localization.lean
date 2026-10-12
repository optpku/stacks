/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.ShortComplex.Ab
public import Mathlib.Topology.LocallyFinsupp
public import stacks_project.Chap75.Definition_75_9_1_Square
public import stacks_project.Chap82.Definition_82_3_1_CycleGroup

/-!
# Localization of cycle groups on algebraic spaces

Fixed-degree cycle maps associated to an open subspace and its reduced closed
complement, packaged as a short complex of abelian groups.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open Function Set

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Hom.Localization

variable {S : Scheme.{u}} {B X : AlgebraicSpace S}
variable (f : X ⟶ B) (δ : Points B → ℤ) (U : OpenSubspace X) (k : ℤ)

/-- Coefficientwise restriction of a cycle along an open immersion has locally
finite support. -/
theorem openPullback_locallyFiniteSupport (α : (AlgebraicGeometry.AlgebraicSpace.Hom.cycleGroup f) δ k) :
    LocallyFiniteSupport fun u : Points U.X ↦
      (α : Function.locallyFinsupp (Points X) ℤ) (Points.map U.ι u) :=
  sorry

/-- The underlying locally finite cycle obtained by restricting coefficients
along `U.ι`. -/
def openPullbackCycle (α : (AlgebraicGeometry.AlgebraicSpace.Hom.cycleGroup f) δ k) :
    Function.locallyFinsupp (Points U.X) ℤ where
  toFun := fun u ↦ (α : Function.locallyFinsupp (Points X) ℤ) (Points.map U.ι u)
  supportWithinDomain' := Set.subset_univ _
  supportLocallyFiniteWithinDomain' := fun u _ ↦
    openPullback_locallyFiniteSupport f δ U k α u

/-- Coefficientwise restriction along `U.ι` preserves the relative degree `k`. -/
theorem openPullback_mem (α : (AlgebraicGeometry.AlgebraicSpace.Hom.cycleGroup f) δ k) :
    openPullbackCycle f δ U k α ∈ (AlgebraicGeometry.AlgebraicSpace.Hom.cycleGroup (U.ι ≫ f)) δ k :=
  sorry

/-- The value of open restriction on a cycle of fixed relative degree. -/
def openPullbackValue (α : (AlgebraicGeometry.AlgebraicSpace.Hom.cycleGroup f) δ k) : (AlgebraicGeometry.AlgebraicSpace.Hom.cycleGroup (U.ι ≫ f)) δ k :=
  ⟨openPullbackCycle f δ U k α, openPullback_mem f δ U k α⟩

/-- Open restriction sends the zero cycle to zero. -/
theorem openPullbackValue_zero : openPullbackValue f δ U k 0 = 0 :=
  sorry

/-- Open restriction preserves addition of cycles. -/
theorem openPullbackValue_add (α β : (AlgebraicGeometry.AlgebraicSpace.Hom.cycleGroup f) δ k) :
    openPullbackValue f δ U k (α + β) =
      openPullbackValue f δ U k α + openPullbackValue f δ U k β :=
  sorry

/-- Restriction of `k`-cycles along the open immersion `U.ι`. -/
def openPullback : (AlgebraicGeometry.AlgebraicSpace.Hom.cycleGroup f) δ k →+ (AlgebraicGeometry.AlgebraicSpace.Hom.cycleGroup (U.ι ≫ f)) δ k where
  toFun := openPullbackValue f δ U k
  map_zero' := openPullbackValue_zero f δ U k
  map_add' := openPullbackValue_add f δ U k

/-- Open restriction evaluates by reading coefficients along `Points.map U.ι`. -/
theorem openPullback_apply (α : (AlgebraicGeometry.AlgebraicSpace.Hom.cycleGroup f) δ k) (u : Points U.X) :
    (openPullback f δ U k α : Function.locallyFinsupp (Points U.X) ℤ) u =
      (α : Function.locallyFinsupp (Points X) ℤ) (Points.map U.ι u) :=
  sorry

/-- Open restriction of `k`-cycles is surjective. -/
theorem openPullback_surjective : Function.Surjective (openPullback f δ U k) :=
  sorry

/-- Open restriction is canonically an epimorphism of abelian groups. -/
instance openPullback_epi : Epi (AddCommGrpCat.ofHom (openPullback f δ U k)) :=
  sorry

/-- Weight-1 closed-immersion pushforward of a cycle has locally finite support. -/
theorem closedPushforward_locallyFiniteSupport
    (α : (AlgebraicGeometry.AlgebraicSpace.Hom.cycleGroup (U.reducedComplement.ι ≫ f)) δ k) :
    LocallyFiniteSupport fun x : Points X ↦
      ∑ᶠ y ∈ Points.map U.reducedComplement.ι ⁻¹' {x},
        (α : Function.locallyFinsupp (Points U.reducedComplement.X) ℤ) y :=
  sorry

/-- The underlying locally finite cycle obtained by weight-1 pushforward along
`U.reducedComplement.ι`. -/
def closedPushforwardCycle (α : (AlgebraicGeometry.AlgebraicSpace.Hom.cycleGroup (U.reducedComplement.ι ≫ f)) δ k) :
    Function.locallyFinsupp (Points X) ℤ where
  toFun := fun x ↦
    ∑ᶠ y ∈ Points.map U.reducedComplement.ι ⁻¹' {x},
      (α : Function.locallyFinsupp (Points U.reducedComplement.X) ℤ) y
  supportWithinDomain' := Set.subset_univ _
  supportLocallyFiniteWithinDomain' := fun x _ ↦
    closedPushforward_locallyFiniteSupport f δ U k α x

/-- Weight-1 pushforward along `U.reducedComplement.ι` preserves the relative
degree `k`. -/
theorem closedPushforward_mem (α : (AlgebraicGeometry.AlgebraicSpace.Hom.cycleGroup (U.reducedComplement.ι ≫ f)) δ k) :
    closedPushforwardCycle f δ U k α ∈ (AlgebraicGeometry.AlgebraicSpace.Hom.cycleGroup f) δ k :=
  sorry

/-- The value of reduced-complement pushforward on a cycle of fixed relative
degree. -/
def closedPushforwardValue (α : (AlgebraicGeometry.AlgebraicSpace.Hom.cycleGroup (U.reducedComplement.ι ≫ f)) δ k) :
    (AlgebraicGeometry.AlgebraicSpace.Hom.cycleGroup f) δ k :=
  ⟨closedPushforwardCycle f δ U k α, closedPushforward_mem f δ U k α⟩

/-- Reduced-complement pushforward sends the zero cycle to zero. -/
theorem closedPushforwardValue_zero : closedPushforwardValue f δ U k 0 = 0 :=
  sorry

/-- Reduced-complement pushforward preserves addition of cycles. -/
theorem closedPushforwardValue_add
    (α β : (AlgebraicGeometry.AlgebraicSpace.Hom.cycleGroup (U.reducedComplement.ι ≫ f)) δ k) :
    closedPushforwardValue f δ U k (α + β) =
      closedPushforwardValue f δ U k α + closedPushforwardValue f δ U k β :=
  sorry

/-- Pushforward of `k`-cycles along the reduced-complement closed immersion. -/
def closedPushforward :
    (AlgebraicGeometry.AlgebraicSpace.Hom.cycleGroup (U.reducedComplement.ι ≫ f)) δ k →+ (AlgebraicGeometry.AlgebraicSpace.Hom.cycleGroup f) δ k where
  toFun := closedPushforwardValue f δ U k
  map_zero' := closedPushforwardValue_zero f δ U k
  map_add' := closedPushforwardValue_add f δ U k

/-- Reduced-complement pushforward evaluates by a weight-1 finsum on the fiber of
`Points.map U.reducedComplement.ι`. -/
theorem closedPushforward_apply (α : (AlgebraicGeometry.AlgebraicSpace.Hom.cycleGroup (U.reducedComplement.ι ≫ f)) δ k)
    (x : Points X) :
    (closedPushforward f δ U k α : Function.locallyFinsupp (Points X) ℤ) x =
      ∑ᶠ y ∈ Points.map U.reducedComplement.ι ⁻¹' {x},
        (α : Function.locallyFinsupp (Points U.reducedComplement.X) ℤ) y :=
  sorry

/-- Pushforward from the reduced complement followed by restriction to the open
subspace is zero. -/
theorem closedPushforward_comp_openPullback :
    AddCommGrpCat.ofHom (closedPushforward f δ U k) ≫
      AddCommGrpCat.ofHom (openPullback f δ U k) = 0 :=
  sorry

/-- The localization short complex of `k`-cycle groups associated to an open
subspace and its reduced closed complement. -/
def complex : ShortComplex Ab.{u + 1} :=
  ShortComplex.mk (AddCommGrpCat.ofHom (closedPushforward f δ U k))
    (AddCommGrpCat.ofHom (openPullback f δ U k))
    (closedPushforward_comp_openPullback f δ U k)

/-- The first arrow of the localization complex is reduced-complement
pushforward. -/
theorem complex_f :
    (complex f δ U k).f = AddCommGrpCat.ofHom (closedPushforward f δ U k) :=
  sorry

/-- The second arrow of the localization complex is open restriction. -/
theorem complex_g :
    (complex f δ U k).g = AddCommGrpCat.ofHom (openPullback f δ U k) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Hom.Localization
