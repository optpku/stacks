module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.KaehlerSquareZero

@[expose] public section

attribute [instance] ModuleCat.Algebra.instModuleCarrier

open CategoryTheory AlgebraicGeometry Functor

universe u

namespace AlgebraicGeometry.GroupoidsOver

/-- The module of Kähler differentials, retained for source compatibility. -/
noncomputable abbrev kaehlerObj {A B : CommRingCat.{u}} (v : A ⟶ B) : ModuleCat.{u} B :=
  CommRingCat.KaehlerDifferential v

/-- The universal differential of an element relative to a ring map. -/
noncomputable abbrev kaehlerD {A B : CommRingCat.{u}} (v : A ⟶ B) (b : B) :
    kaehlerObj v :=
  (CommRingCat.KaehlerDifferential.D v).d b

#check (AlgebraicGeometry.GroupoidsOver.trivSqZeroCan :
  {A B : CommRingCat.{u}} → (v : A ⟶ B) →
    B ⟶ trivSqZero B (CommRingCat.KaehlerDifferential v))

#check (AlgebraicGeometry.GroupoidsOver.specOverCan :
  {A B : CommRingCat.{u}} → (v : A ⟶ B) →
    {S : Scheme.{u}} → {σA : Spec A ⟶ S} → {σB : Spec B ⟶ S} →
    (Spec.map v ≫ σA = σB) →
    (Over.mk (specTrivSqZero σB (CommRingCat.KaehlerDifferential v)) ⟶ Over.mk σB))

end AlgebraicGeometry.GroupoidsOver
