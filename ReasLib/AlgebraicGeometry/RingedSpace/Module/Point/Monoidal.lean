module

public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Adjunction
public import Mathlib.CategoryTheory.Adjunction.Unique
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Indiscrete.Monoidal
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Monoidal
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Point
import Mathlib.Tactic.CrossRefAttribute

/-!
# Monoidal module sheaves on a ringed point

Scalar transport from the coefficient ring to the top-open ring is identified with extension
of scalars along the inverse ring isomorphism.  Transporting the canonical strong-monoidal
structure across this identification and composing with generation from the top open makes the
point-module functor strong monoidal.
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace
open CategoryTheory.MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.RingedPoint.Module

variable (R : Type u) [CommRing R]

/-- The top-open ring underlying the commutative structure sheaf of a ringed point retains its
canonical commutative ring structure. -/
@[stacks 01BH "commutative top-open ring of a ringed point", implicit_reducible]
noncomputable instance topRingCommRing :
    CommRing ((RingedPoint.ringCatSheaf R).obj.obj
      (op (⊤ : Opens RingedPoint.carrier))) :=
  TopCat.Sheaf.ringSheafOfComm.commRing (RingedPoint.structureSheaf R) (op ⊤)

/-- Modules over the top-open ring of a ringed point carry the canonical tensor product. -/
@[stacks 01BH "tensor products over the top-open ring", implicit_reducible]
noncomputable instance topModulesMonoidal :
    MonoidalCategory
      (ModuleCat.{u} ((RingedPoint.ringCatSheaf R).obj.obj
        (op (⊤ : Opens RingedPoint.carrier)))) :=
  ModuleCat.monoidalCategory

/-- Extension of scalars from `R` to the top-open ring is canonically strong monoidal. -/
@[stacks 01BH "monoidal extension to the top-open ring", implicit_reducible]
noncomputable instance topExtendScalarsMonoidal :
    (ModuleCat.extendScalars
      (RingedPoint.topRingIso R).ringCatIsoToRingEquiv.symm.toRingHom).Monoidal :=
  ModuleCat.instMonoidalExtendScalars _

/-- Generation of module sheaves from the top open of a ringed point is canonically strong
monoidal. -/
@[stacks 01BH "monoidal generation from the top open", implicit_reducible]
noncomputable instance topGenerationMonoidal :
    (SheafOfModules.Indiscrete.ofTopFunctor
      (RingedPoint.ringCatSheaf R)).Monoidal :=
  SheafOfModules.Indiscrete.ofTopFunctorMonoidal (RingedPoint.structureSheaf R)

/-- Restriction of scalars along the top-open ring isomorphism is naturally isomorphic to
extension of scalars along its inverse. -/
@[stacks 01BH "top-open scalar transport"]
noncomputable def topEquivalenceFunctorIso :
    ModuleCat.extendScalars
        (RingedPoint.topRingIso R).ringCatIsoToRingEquiv.symm.toRingHom ≅
      (topEquivalence R).functor :=
  Adjunction.leftAdjointUniq
    (ModuleCat.extendRestrictScalarsAdj
      (RingedPoint.topRingIso R).ringCatIsoToRingEquiv.symm.toRingHom)
    (topEquivalence R).toAdjunction

/-- Scalar transport from `R` to the top-open ring of `RingedPoint.of R` is canonically strong
monoidal. -/
@[stacks 01BH "strong-monoidal top-open scalar transport", implicit_reducible]
noncomputable instance topEquivalenceMonoidal :
    ((topEquivalence R).functor).Monoidal :=
  @Functor.Monoidal.transport
    (ModuleCat.{u} R) _ ModuleCat.monoidalCategory
    (ModuleCat.{u} ((RingedPoint.ringCatSheaf R).obj.obj
      (op (⊤ : Opens RingedPoint.carrier)))) _ (topModulesMonoidal R)
    _ _ (topExtendScalarsMonoidal R) (topEquivalenceFunctorIso R)

/-- Forming the module sheaf on `RingedPoint.of R` is canonically strong monoidal. -/
@[stacks 01BH "strong-monoidal point-module functor", implicit_reducible]
noncomputable instance functorMonoidal : (functor R).Monoidal :=
  inferInstanceAs
    (((topEquivalence R).functor ⋙
      SheafOfModules.Indiscrete.ofTopFunctor (RingedPoint.ringCatSheaf R)).Monoidal)

/-- The tensorator of the point-module functor, bundled as a natural isomorphism. -/
@[stacks 01BH "point-module tensor natural isomorphism"]
noncomputable abbrev tensorNatIso :
    Functor.prod (functor R) (functor R) ⋙
        MonoidalCategory.tensor (RingedPoint.of R).Modules ≅
      MonoidalCategory.tensor (ModuleCat.{u} R) ⋙ functor R :=
  Functor.Monoidal.μNatIso (functor R)

/-- The canonical tensor-product isomorphism for module sheaves on a ringed point. -/
@[stacks 01BH "point-module tensor product"]
noncomputable abbrev tensorIso (M N : ModuleCat.{u} R) :
    sheaf R M ⊗ sheaf R N ≅ sheaf R (M ⊗ N) :=
  (tensorNatIso R).app (M, N)

/-- The canonical tensor-unit isomorphism for module sheaves on a ringed point. -/
@[stacks 01BH "point-module tensor unit"]
noncomputable abbrev unitIso :
    𝟙_ (RingedPoint.of R).Modules ≅ sheaf R (𝟙_ (ModuleCat.{u} R)) :=
  Functor.Monoidal.εIso (functor R)

#synth (functor R).Monoidal

end AlgebraicGeometry.RingedPoint.Module
