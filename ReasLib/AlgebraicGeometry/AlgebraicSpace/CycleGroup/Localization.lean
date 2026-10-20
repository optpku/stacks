/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.ShortComplex.Ab
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CycleGroup.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.OpenSubspace.Complement
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.UniversallyCatenary
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation
public import ReasLib.Topology.Specialization.Dimension

/-!
# Localization of cycle groups on algebraic spaces

Fixed-degree cycle maps associated to an open subspace and its reduced closed
complement, packaged as a short complex of abelian groups.
-/

public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open Function Set

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The group of degree-`k` cycles on an open subspace, relative to the
composite structure morphism and the dimension function `δ` on the base. -/
abbrev OpenSubspace.cycleGroup {S : Scheme.{u}} {B X : AlgebraicSpace S}
    (U : OpenSubspace X) (f : X ⟶ B) [LocallyOfFiniteType f]
    (δ : Points B → ℤ) (k : ℤ) :
    AddSubgroup (Function.locallyFinsupp (Points U.X) ℤ) :=
  @Hom.cycleGroup S B U.X (U.ι ≫ f)
    (locallyOfFiniteType_openSubspace_comp U f) δ k

/-- The group of degree-`k` cycles on a closed subspace, relative to the
composite structure morphism and the dimension function `δ` on the base. -/
abbrev ClosedSubspace.cycleGroup {S : Scheme.{u}} {B X : AlgebraicSpace S}
    (W : ClosedSubspace X) (f : X ⟶ B) [LocallyOfFiniteType f]
    (δ : Points B → ℤ) (k : ℤ) :
    AddSubgroup (Function.locallyFinsupp (Points W.X) ℤ) :=
  @Hom.cycleGroup S B W.X (W.ι ≫ f)
    (locallyOfFiniteType_closedSubspace_comp W f) δ k

namespace Hom.Localization

variable {S : Scheme.{u}} {B X : AlgebraicSpace S}
variable (f : X ⟶ B) [LocallyOfFiniteType f] (δ : Points B → ℤ) (U : OpenSubspace X) (k : ℤ)

/-- Coefficientwise restriction of a cycle along an open immersion has locally
finite support. -/
private theorem openPullback_locallyFiniteSupport (α : Hom.cycleGroup f δ k) :
    LocallyFiniteSupport fun u : Points U.X ↦
      (α : Function.locallyFinsupp (Points X) ℤ) (Points.map U.ι u) :=
  sorry

/-- The underlying locally finite cycle obtained by restricting coefficients
along `U.ι`. -/
private def openPullbackCycle (α : Hom.cycleGroup f δ k) :
    Function.locallyFinsupp (Points U.X) ℤ where
  toFun := fun u ↦ (α : Function.locallyFinsupp (Points X) ℤ) (Points.map U.ι u)
  supportWithinDomain' := Set.subset_univ _
  supportLocallyFiniteWithinDomain' := fun u _ ↦
    openPullback_locallyFiniteSupport f δ U k α u

/-- Coefficientwise restriction along `U.ι` preserves the relative degree `k`. -/
private theorem openPullback_mem (α : Hom.cycleGroup f δ k) :
    openPullbackCycle f δ U k α ∈ U.cycleGroup f δ k :=
  sorry

/-- The value of open restriction on a cycle of fixed relative degree. -/
private def openPullbackValue (α : Hom.cycleGroup f δ k) : U.cycleGroup f δ k :=
  ⟨openPullbackCycle f δ U k α, openPullback_mem f δ U k α⟩

/-- Open restriction sends the zero cycle to zero. -/
private theorem openPullbackValue_zero : openPullbackValue f δ U k 0 = 0 :=
  sorry

/-- Open restriction preserves addition of cycles. -/
private theorem openPullbackValue_add (α β : Hom.cycleGroup f δ k) :
    openPullbackValue f δ U k (α + β) =
      openPullbackValue f δ U k α + openPullbackValue f δ U k β :=
  sorry

/-- Restriction of `k`-cycles along the open immersion `U.ι`. -/
@[expose] def openPullback : Hom.cycleGroup f δ k →+ U.cycleGroup f δ k where
  toFun := fun α ↦
    ⟨{ toFun := fun u ↦
          (α : Function.locallyFinsupp (Points X) ℤ) (Points.map U.ι u)
       supportWithinDomain' := Set.subset_univ _
       supportLocallyFiniteWithinDomain' := by
         intro u _
         exact openPullback_locallyFiniteSupport f δ U k α u },
      by exact openPullback_mem f δ U k α⟩
  map_zero' := by exact openPullbackValue_zero f δ U k
  map_add' := by
    intro α β
    exact openPullbackValue_add f δ U k α β

/-- Open restriction evaluates by reading coefficients along `Points.map U.ι`. -/
theorem openPullback_apply (α : Hom.cycleGroup f δ k) (u : Points U.X) :
    (openPullback f δ U k α : Function.locallyFinsupp (Points U.X) ℤ) u =
      (α : Function.locallyFinsupp (Points X) ℤ) (Points.map U.ι u) :=
  sorry

/-- For a quasi-separated algebraic space locally of finite type over a
quasi-separated universally catenary base with dimension function `δ`,
restriction of degree-`k` cycles to an open subspace is surjective. -/
theorem openPullback_surjective {S : Scheme.{u}} {B X : AlgebraicSpace S}
    [UniversallyCatenary B] [IsQuasiSeparated B]
    (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (U : OpenSubspace X) (k : ℤ) : Function.Surjective (openPullback f δ U k) :=
  sorry

/-- Weight-1 closed-immersion pushforward of a cycle has locally finite support. -/
private theorem closedPushforward_locallyFiniteSupport
    (α : U.reducedComplement.cycleGroup f δ k) :
    LocallyFiniteSupport fun x : Points X ↦
      ∑ᶠ y ∈ Points.map U.reducedComplement.ι ⁻¹' {x},
        (α : Function.locallyFinsupp (Points U.reducedComplement.X) ℤ) y :=
  sorry

/-- The underlying locally finite cycle obtained by weight-1 pushforward along
`U.reducedComplement.ι`. -/
private def closedPushforwardCycle (α : U.reducedComplement.cycleGroup f δ k) :
    Function.locallyFinsupp (Points X) ℤ where
  toFun := fun x ↦
    ∑ᶠ y ∈ Points.map U.reducedComplement.ι ⁻¹' {x},
      (α : Function.locallyFinsupp (Points U.reducedComplement.X) ℤ) y
  supportWithinDomain' := Set.subset_univ _
  supportLocallyFiniteWithinDomain' := fun x _ ↦
    closedPushforward_locallyFiniteSupport f δ U k α x

/-- Weight-1 pushforward along `U.reducedComplement.ι` preserves the relative
degree `k`. -/
private theorem closedPushforward_mem (α : U.reducedComplement.cycleGroup f δ k) :
    closedPushforwardCycle f δ U k α ∈ Hom.cycleGroup f δ k :=
  sorry

/-- The value of reduced-complement pushforward on a cycle of fixed relative
degree. -/
private def closedPushforwardValue (α : U.reducedComplement.cycleGroup f δ k) :
    Hom.cycleGroup f δ k :=
  ⟨closedPushforwardCycle f δ U k α, closedPushforward_mem f δ U k α⟩

/-- Reduced-complement pushforward sends the zero cycle to zero. -/
private theorem closedPushforwardValue_zero : closedPushforwardValue f δ U k 0 = 0 :=
  sorry

/-- Reduced-complement pushforward preserves addition of cycles. -/
private theorem closedPushforwardValue_add
    (α β : U.reducedComplement.cycleGroup f δ k) :
    closedPushforwardValue f δ U k (α + β) =
      closedPushforwardValue f δ U k α + closedPushforwardValue f δ U k β :=
  sorry

/-- Pushforward of `k`-cycles along the reduced-complement closed immersion. -/
def closedPushforward :
    U.reducedComplement.cycleGroup f δ k →+ Hom.cycleGroup f δ k where
  toFun := closedPushforwardValue f δ U k
  map_zero' := closedPushforwardValue_zero f δ U k
  map_add' := closedPushforwardValue_add f δ U k

/-- Reduced-complement pushforward evaluates by a weight-1 finsum on the fiber of
`Points.map U.reducedComplement.ι`. -/
theorem closedPushforward_apply (α : U.reducedComplement.cycleGroup f δ k)
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
@[expose] def complex : ShortComplex Ab.{u + 1} :=
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

/-- For a quasi-separated algebraic space locally of finite type over a
quasi-separated universally catenary base with dimension function `δ`,
pushforward from the reduced closed complement and restriction to an open
subspace form an exact sequence of degree-`k` cycle groups, with surjective
restriction. -/
theorem exact {S : Scheme.{u}} {B X : AlgebraicSpace S}
    [UniversallyCatenary B] [IsQuasiSeparated B]
    (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (U : OpenSubspace X) (k : ℤ) :
    (complex f δ U k).Exact ∧ Epi (complex f δ U k).g :=
  sorry

end Hom.Localization

end AlgebraicGeometry.AlgebraicSpace
