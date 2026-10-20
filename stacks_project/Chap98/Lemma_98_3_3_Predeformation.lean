module

public import ReasLib.AlgebraicGeometry.FormalDeformation.Predeformation.TwoFibreProduct

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.GroupoidsOver.Predeformation
open scoped Bicategory

universe u

section

variable {S : Scheme.{u}} [IsLocallyNoetherian S]
variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable (openImmersion : Spec (CommRingCat.of Λ) ⟶ S) [IsOpenImmersion openImmersion]
variable (kToS : Spec (CommRingCat.of k) ⟶ S) [LocallyOfFiniteType kToS]
variable (h_factor : Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ openImmersion = kToS)

#check (AlgebraicGeometry.GroupoidsOver.Predeformation.bundled openImmersion kToS h_factor :
  (X : GroupoidsOver S) → X.p.Fiber (Over.mk kToS) →
    CofiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u} (ArtinianLocalAlgCat Λ k))

#check (AlgebraicGeometry.GroupoidsOver.Predeformation.mapBundled openImmersion kToS h_factor :
  {X Y : GroupoidsOver S} → (φ : X ⟶ Y) → (x0 : X.p.Fiber (Over.mk kToS)) →
    bundled openImmersion kToS h_factor X x0 ⟶
      bundled openImmersion kToS h_factor Y (residueImage φ x0))

#check (AlgebraicGeometry.GroupoidsOver.Predeformation.mapAlong openImmersion kToS h_factor :
  {X Y : GroupoidsOver S} → (φ : X ⟶ Y) →
    {x0 : X.p.Fiber (Over.mk kToS)} → {y0 : Y.p.Fiber (Over.mk kToS)} →
    (α : residueImage φ x0 ≅ y0) →
      (bundled openImmersion kToS h_factor X x0 ⟶ bundled openImmersion kToS h_factor Y y0))

end
