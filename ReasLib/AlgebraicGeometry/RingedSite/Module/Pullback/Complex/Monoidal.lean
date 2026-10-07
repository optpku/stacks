module

public import ReasLib.Algebra.Homology.CochainComplex.Monoidal.Functor
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Complex.Monoidal
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Pullback.Complex
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Pullback.Monoidal
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.InternalHom
import Mathlib.Tactic.CrossRefAttribute

/-!
# Monoidal pullback of complexes on ringed sites

Pullback of modules on a commutative ringed-site presentation is a left adjoint and is strong
monoidal.  Its degreewise action on unbounded cochain complexes therefore preserves the coproducts
used by totalization, so the generic cochain tensor comparison is automatically invertible.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory ComplexShape

noncomputable section

universe uX vX uY vY w

namespace RingedSite.Hom.modulePullbackComplex

variable {CX : Type uX} [Category.{vX} CX]
variable {CY : Type uY} [Category.{vY} CY]
variable {JX : GrothendieckTopology CX} {JY : GrothendieckTopology CY}
variable [JX.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable [JY.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable [HasWeakSheafify JX AddCommGrpCat.{w}]
variable [JX.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [HasWeakSheafify JY AddCommGrpCat.{w}]
variable [JY.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [UnivLE.{max uX vX, w}] [UnivLE.{max uY vY, w}]
variable {OX : Sheaf JX CommRingCat.{w}} {OY : Sheaf JY CommRingCat.{w}}

variable (f : RingedSite.Hom (RingedSite.ofCommRingSheaf JX OX)
  (RingedSite.ofCommRingSheaf JY OY))
variable [(PresheafOfModules.pushforward.{w} f.structureSheafMap.hom).IsRightAdjoint]

/-- The tensor comparison for degreewise module pullback is invertible because module pullback,
as a left adjoint, preserves the coproducts used by totalization. -/
@[stacks 07A4 "complex pullback tensor comparison", instance]
theorem tensorComparisonIsIso (K L : CochainComplex
    (RingedSite.ModuleCat.{w} (RingedSite.ofCommRingSheaf JY OY)) ℤ) :
    IsIso (Functor.Cochain.tensorComparison f.modulePullback.{w} K L) := sorry

/-- Degreewise pullback of unbounded cochain complexes is canonically strong monoidal. -/
@[stacks 07A4 "monoidal complex pullback", implicit_reducible]
noncomputable instance monoidal : f.modulePullbackComplex.{w}.Monoidal :=
  (Functor.Cochain.coreMonoidal f.modulePullback.{w}).toMonoidal

/-- The canonical unit isomorphism for pullback of unbounded cochain complexes. -/
@[stacks 07A4 "complex pullback unit"]
noncomputable abbrev unitIso :
    𝟙_ (CochainComplex
        (RingedSite.ModuleCat.{w} (RingedSite.ofCommRingSheaf JX OX)) ℤ) ≅
      f.modulePullbackComplex.{w}.obj
        (𝟙_ (CochainComplex
          (RingedSite.ModuleCat.{w} (RingedSite.ofCommRingSheaf JY OY)) ℤ)) :=
  Functor.Monoidal.εIso f.modulePullbackComplex.{w}

/-- The canonical tensorator for pullback of unbounded cochain complexes. -/
@[stacks 07A4 "complex pullback tensorator"]
noncomputable abbrev tensorIso
    (K L : CochainComplex
      (RingedSite.ModuleCat.{w} (RingedSite.ofCommRingSheaf JY OY)) ℤ) :
    f.modulePullbackComplex.{w}.obj K ⊗ f.modulePullbackComplex.{w}.obj L ≅
      f.modulePullbackComplex.{w}.obj (K ⊗ L) :=
  Functor.Monoidal.μIso f.modulePullbackComplex.{w} K L

#synth Functor.Cochain.HasMappedTensorTotals f.modulePullback.{w}
#synth f.modulePullbackComplex.{w}.Monoidal

end RingedSite.Hom.modulePullbackComplex
