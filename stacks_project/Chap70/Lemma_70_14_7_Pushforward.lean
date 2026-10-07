module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import stacks_project.Chap67.Definition_67_4_2_Separation
public import stacks_project.Chap70.Lemma_70_14_5_SectionsWithSupport

/-!
# Pushforward of sections supported on a closed subset

For a quasi-compact and quasi-separated morphism of algebraic spaces, pushforward preserves the
kernel subsheaf of sections supported in the closed complement of a quasi-compact open immersion.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

/-- For a quasi-compact and quasi-separated morphism `f : X ⟶ Y` of algebraic spaces and a
quasi-compact open immersion `ιV : V ⟶ Y`, if `ιU : U ⟶ X` is an open immersion fitting in a
cartesian square over `ιV`, then on every object of the small étale site of `Y` the image of
`f_*` of the supported-sections inclusion of `F` along `ιU` equals the image of the
supported-sections inclusion of `f_* F` along `ιV`. -/
theorem range_pushforward_sectionsWithSupportInι_app_eq
    {S : Scheme.{u}} {X Y U V : AlgebraicSpace S}
    (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    (ιV : V ⟶ Y) [IsOpenImmersion ιV] [QuasiCompact ιV]
    (ιU : U ⟶ X) [IsOpenImmersion ιU] (f' : U ⟶ V)
    (h_cart : IsPullback ιU f' f ιV)
    (F : X.Modules) [F.IsQuasicoherent]
    (W : smallEtaleSite Y) :
    Set.range (((pushforward f).map (sectionsWithSupportInι ιU F)).val.app (op W)) =
      Set.range ((sectionsWithSupportInι ιV ((pushforward f).obj F)).val.app (op W)) :=
  sorry

/-- If `T` is the closed complement of the image of `Points.map ιV` and `ιU : U ⟶ X` fits in a
cartesian square over `ιV : V ⟶ Y`, then the inverse image of `T` under `Points.map f` is the
closed complement of the image of `Points.map ιU`. -/
theorem preimage_closedComplement_eq
    {S : Scheme.{u}} {X Y U V : AlgebraicSpace S}
    (f : X ⟶ Y) (ιV : V ⟶ Y) (ιU : U ⟶ X) (f' : U ⟶ V)
    (h_cart : IsPullback ιU f' f ιV)
    {T : Set (Points Y)} (hT : T = (Set.range (Points.map ιV))ᶜ) :
    Points.map f ⁻¹' T = (Set.range (Points.map ιU))ᶜ :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
