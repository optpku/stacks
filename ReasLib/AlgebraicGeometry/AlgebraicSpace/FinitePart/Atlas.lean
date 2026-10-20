module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FinitePart.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Etale
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.LocallyQuasiFinite

/-!
# Étale atlases of finite-part functors
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry MorphismProperty

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.FinitePart

/-- The finite-part functor of a separated locally quasi-finite morphism of
algebraic spaces admits a representable surjective étale morphism from a scheme
that is étale over the target algebraic space. -/
theorem exists_surjective_etale {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [AlgebraicSpace.Separated f] [AlgebraicSpace.LocallyQuasiFinite f] :
    ∃ (U : Over S) (a : ofOver U ⟶ Y) (φ : yoneda.obj U ⟶ functor f),
      AlgebraicSpace.Etale a ∧ φ ≫ hom f = a ∧
        (over (@AlgebraicGeometry.Etale : MorphismProperty Scheme.{u})).presheaf φ ∧
        (over (@AlgebraicGeometry.Surjective : MorphismProperty Scheme.{u})).presheaf φ :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.FinitePart
