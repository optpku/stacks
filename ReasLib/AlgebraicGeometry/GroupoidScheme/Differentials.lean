module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import ReasLib.AlgebraicGeometry.GroupoidScheme.Pullback
public import ReasLib.AlgebraicGeometry.Scheme.Differentials.Conormal
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Sections

/-!
# Differentials of a groupoid scheme

This module constructs the canonical morphism from the target pullback of the conormal sheaf of
the identity section to the relative differentials of the target map of a groupoid scheme.
-/

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidScheme.Differentials

/-- The identity morphism of a groupoid scheme is an immersion. -/
theorem identity_isImmersion {S : Scheme.{u}} (G : GroupoidScheme S) :
    IsImmersion G.e.left :=
  Scheme.Hom.Section.isImmersion (by
    simpa using congrArg Over.Hom.left G.identity_source)

/-- The target map followed by the identity section and source map is again the target map. -/
theorem target_comp_identity_comp_source {S : Scheme.{u}} (G : GroupoidScheme S) :
    (G.t.left ≫ G.e.left) ≫ G.s.left = G.t.left := by
  have h_identity_source : G.e.left ≫ G.s.left = 𝟙 G.U.left := by
    simpa using congrArg Over.Hom.left G.identity_source
  simpa [Category.assoc] using congrArg (fun k ↦ G.t.left ≫ k) h_identity_source

/-- The groupoid identity law identifies the two relative-differentials objects used by the
identity-restriction comparison. -/
theorem identityRestrictionTransport_eq {S : Scheme.{u}} (G : GroupoidScheme S) :
    Ω[((G.t.left ≫ G.e.left) ≫ G.s.left).toShHom] = Ω[G.t.left.toShHom] := by
  simpa using congrArg (fun f ↦ Ω[f.toShHom]) (target_comp_identity_comp_source G)

/-- The transport from the relative differentials of `(t ≫ e) ≫ s` to those of `t`. -/
def identityRestrictionTransport {S : Scheme.{u}} (G : GroupoidScheme S) :
    Ω[((G.t.left ≫ G.e.left) ≫ G.s.left).toShHom] ⟶
      Ω[G.t.left.toShHom] :=
  eqToHom (identityRestrictionTransport_eq G)

/-- The pullback of the identity-section relative-differentials term along the target map,
transported to the target-relative differentials using the groupoid identity law. -/
def identityRestrictionComparison {S : Scheme.{u}} (G : GroupoidScheme S) :
    (Scheme.Modules.pullback G.t.left).obj
        ((Scheme.Modules.pullback G.e.left).obj Ω[G.s.left.toShHom]) ⟶
      Ω[G.t.left.toShHom] :=
  (Scheme.Modules.pullbackComp G.t.left G.e.left).hom.app Ω[G.s.left.toShHom] ≫
    Scheme.Hom.Conormal.Differentials.comparison (G.t.left ≫ G.e.left) G.s.left ≫
      identityRestrictionTransport G

/-- The canonical morphism from the target pullback of the identity conormal sheaf to the
relative differentials of the target map. -/
def conormalComparison {S : Scheme.{u}} (G : GroupoidScheme S) :
    (Scheme.Modules.pullback G.t.left).obj (Scheme.Hom.conormalSheaf G.e.left) ⟶
      Ω[G.t.left.toShHom] :=
  (Scheme.Modules.pullback G.t.left).map
      (Scheme.Hom.Conormal.Differentials.map G.e.left G.s.left) ≫
    identityRestrictionComparison G

/-- The groupoid conormal comparison is the target pullback of the identity-section
conormal-differentials map followed by the identity-restriction comparison. -/
theorem conormalComparison_spec {S : Scheme.{u}} (G : GroupoidScheme S) :
    conormalComparison G =
      (Scheme.Modules.pullback G.t.left).map
          (Scheme.Hom.Conormal.Differentials.map G.e.left G.s.left) ≫
        identityRestrictionComparison G := rfl

/-- The groupoid conormal comparison is an epimorphism. -/
theorem conormalComparison_epi {S : Scheme.{u}} (G : GroupoidScheme S) :
    Epi (conormalComparison G) := sorry

/-- Flatness of the source map makes the groupoid conormal comparison an isomorphism. -/
theorem conormalComparison_isIso {S : Scheme.{u}} (G : GroupoidScheme S)
    [Flat G.s.left] : IsIso (conormalComparison G) := sorry

end AlgebraicGeometry.GroupoidScheme.Differentials
