module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Basic
public import ReasLib.CategoryTheory.Fibered.BasedCategory.InGroupoids.PseudoPullback
public import ReasLib.CategoryTheory.Fibered.Representable.Slice.Map
public import ReasLib.CategoryTheory.Fibered.TwoFibreProduct.FullSubbicategory.Lift

/-!
# Scheme-induced base changes of categories fibred in groupoids

Fibre products with scheme slices have canonical projections and maps induced by
commuting morphisms of schemes over the base.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Bicategory
open FiberedCategoryOver.Groupoids (overMap)
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- The two-fibre product with the slice morphism induced by a scheme morphism. -/
abbrev pullbackAlongOver {S : Scheme.{u}} {X : GroupoidsOver S} {Y Z : Over S}
    (f : X ⟶ GroupoidsOver.slice Y) (g : Z ⟶ Y) : GroupoidsOver S :=
  TwoFibreProduct.apex.{u + 1, u, u + 1, u} f (overMap g)

/-- The first projection from the scheme-induced two-fibre product. -/
abbrev pullbackAlongOver.fst {S : Scheme.{u}} {X : GroupoidsOver S}
    {Y Z : Over S} (f : X ⟶ GroupoidsOver.slice Y) (g : Z ⟶ Y) :
    pullbackAlongOver f g ⟶ X :=
  TwoFibreProduct.fst.{u + 1, u, u + 1, u} f (overMap g)

/-- The second projection from the scheme-induced two-fibre product. -/
abbrev pullbackAlongOver.snd {S : Scheme.{u}} {X : GroupoidsOver S}
    {Y Z : Over S} (f : X ⟶ GroupoidsOver.slice Y) (g : Z ⟶ Y) :
    pullbackAlongOver f g ⟶ GroupoidsOver.slice Z :=
  TwoFibreProduct.snd.{u + 1, u, u + 1, u} f (overMap g)

/-- A commuting morphism of schemes over the target induces a morphism of
two-fibre products, preserving the first leg and postcomposing the second leg. -/
def pullbackAlongOver.map {S : Scheme.{u}} {X : GroupoidsOver S}
    {Y Z₁ Z₂ : Over S} (f : X ⟶ GroupoidsOver.slice Y)
    (g₁ : Z₁ ⟶ Y) (g₂ : Z₂ ⟶ Y) (a : Z₁ ⟶ Z₂) (ha : a ≫ g₂ = g₁) :
    pullbackAlongOver f g₁ ⟶ pullbackAlongOver f g₂ :=
  TwoFibreProduct.lift
    (PseudoPullbackCone.mk f (overMap g₂) (pullbackAlongOver f g₁)
      (pullbackAlongOver.fst f g₁) (pullbackAlongOver.snd f g₁ ≫ overMap a)
      (TwoFibreProduct.comparisonIso f (overMap g₁) ≪≫
        whiskerLeftIso (pullbackAlongOver.snd f g₁)
          (eqToIso (congrArg overMap ha.symm) ≪≫ eqToIso (overMap.comp a g₂)) ≪≫
        (α_ (pullbackAlongOver.snd f g₁) (overMap a) (overMap g₂)).symm))

/-- The induced base-change morphism commutes with the first projection. -/
def pullbackAlongOver.map.fstIso {S : Scheme.{u}} {X : GroupoidsOver S}
    {Y Z₁ Z₂ : Over S} (f : X ⟶ GroupoidsOver.slice Y)
    (g₁ : Z₁ ⟶ Y) (g₂ : Z₂ ⟶ Y) (a : Z₁ ⟶ Z₂) (ha : a ≫ g₂ = g₁) :
    pullbackAlongOver.map f g₁ g₂ a ha ≫ pullbackAlongOver.fst f g₂ ≅
      pullbackAlongOver.fst f g₁ :=
  TwoFibreProduct.lift.fstIso _

/-- The second projection of the induced base-change morphism is the original
second projection followed by the canonical slice morphism. -/
def pullbackAlongOver.map.sndIso {S : Scheme.{u}} {X : GroupoidsOver S}
    {Y Z₁ Z₂ : Over S} (f : X ⟶ GroupoidsOver.slice Y)
    (g₁ : Z₁ ⟶ Y) (g₂ : Z₂ ⟶ Y) (a : Z₁ ⟶ Z₂) (ha : a ≫ g₂ = g₁) :
    pullbackAlongOver.map f g₁ g₂ a ha ≫ pullbackAlongOver.snd f g₂ ≅
      pullbackAlongOver.snd f g₁ ≫ overMap a :=
  TwoFibreProduct.lift.sndIso _

end AlgebraicGeometry.AlgebraicStack
