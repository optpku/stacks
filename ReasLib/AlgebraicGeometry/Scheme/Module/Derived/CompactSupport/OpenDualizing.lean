module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.ProperDualizingComplex.NormalizedPairing
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Pullback.Composition

/-!
# Structure-sheaf-normalized dualizing objects on a fixed proper compactification

For p=j≫q with j open and q proper, the compactification model of p!O is
the actual derived restriction of the adjunction-defined q!O. Restriction
between nested opens uses the specified derived-pullback compositor.
-/

@[expose] public section
open AlgebraicGeometry CategoryTheory

noncomputable section
universe u

namespace AlgebraicGeometry.Scheme.ModuleDerived.CompactSupport

variable {k : Type u} [Field k] {X U U' : Scheme.{u}}
variable (q : X ⟶ Spec (CommRingCat.of k)) [IsProper q]
variable (j : U ⟶ X) [IsOpenImmersion j]

/-- The unbounded compactification model of upper shriek, using the actual
proper adjunction right adjoint followed by open pullback. -/
def compactificationShriekModel :
    Scheme.DerivedQCoh (Spec (CommRingCat.of k)) ⥤ Scheme.DerivedQCoh U :=
  (Scheme.DerivedQCoh.pushforwardCohomologyIn q).rightAdjoint ⋙
    Scheme.DerivedQCoh.pullback j

/-- The dualizing object normalized at O_Spec(k) for this proper compactification. -/
def openDualizing : RingedSpace.ModuleDerived U.toRingedSpace :=
  (RingedSpace.modulePullbackDerived j.toShHom).obj
    (Scheme.DerivedQCoh.properDualizingComplex q).obj

/-- Applying the actual compactification upper-shriek model to the base
structure sheaf gives exactly the specified open dualizing object. -/
theorem openDualizing_eq_compactificationModel :
    openDualizing q j =
      ((compactificationShriekModel q j).obj
        (Scheme.DerivedQCoh.structureSheaf (Spec (CommRingCat.of k)))).obj := rfl

/-- Nested-open restriction of q!O uses the canonical pullback compositor,
not a selected isomorphism between dualizing objects. -/
def openDualizingRestrictionIso (i : U' ⟶ U) [IsOpenImmersion i] :
    (RingedSpace.modulePullbackDerived i.toShHom).obj (openDualizing q j) ≅
      openDualizing q (i ≫ j) :=
  (RingedSpace.modulePullbackDerived.compIso i.toShHom j.toShHom
    (RingedSpace.modulePullbackDerived.compComparison_isIso i.toShHom j.toShHom)).app
      (Scheme.DerivedQCoh.properDualizingComplex q).obj

/-- The forward nested-open map is the specified compositor at q!O. -/
theorem openDualizingRestrictionIso_hom (i : U' ⟶ U) [IsOpenImmersion i] :
    (openDualizingRestrictionIso q j i).hom =
      (RingedSpace.modulePullbackDerived.compComparison i.toShHom j.toShHom).app
        (Scheme.DerivedQCoh.properDualizingComplex q).obj := rfl

end AlgebraicGeometry.Scheme.ModuleDerived.CompactSupport
