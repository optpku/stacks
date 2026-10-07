module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.BaseChange.Map
public import ReasLib.CategoryTheory.Adjunction.BaseChange.HorizontalComposition

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale.BaseChange

/-- The canonical derived base-change component for the outer rectangle is the horizontal
composition of the two canonical components. -/
theorem derivedMap_comp
    {W Z X Y S T : Scheme.{u}}
    (i : W ⟶ X) (j : Z ⟶ W) (k : Z ⟶ Y) (f : X ⟶ S)
    (h : Y ⟶ X) (e : Y ⟶ T) (g : T ⟶ S)
    (h₁ : IsPullback j k i h) (h₀ : IsPullback h e f g)
    (K : DerivedCategory (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})) :
    derivedMap (i ≫ f) j (k ≫ e) g (h₁.paste_vert h₀) K =
      (Derived.inverseImageCompIso i f).hom.app ((Derived.directImage g).obj K) ≫
        (Derived.inverseImage i).map (derivedMap f h e g h₀ K) ≫
        derivedMap i j k h h₁ ((Derived.inverseImage e).obj K) ≫
        (Derived.directImage j).map
          ((Derived.inverseImageCompIso k e).inv.app K) := sorry

/-- The canonical degreewise higher-direct-image component for the outer rectangle is the
horizontal composition of the two canonical degreewise components. -/
theorem higherMap_comp
    {W Z X Y S T : Scheme.{u}}
    (i : W ⟶ X) (j : Z ⟶ W) (k : Z ⟶ Y) (f : X ⟶ S)
    (h : Y ⟶ X) (e : Y ⟶ T) (g : T ⟶ S)
    (h₁ : IsPullback j k i h) (h₀ : IsPullback h e f g) (q : ℕ)
    (F : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    higherMap (i ≫ f) j (k ≫ e) g (h₁.paste_vert h₀) q F =
      (Abelian.inverseImageCompIso i f).hom.app ((Derived.higherDirectImage g q).obj F) ≫
        (Abelian.inverseImage i).map (higherMap f h e g h₀ q F) ≫
        higherMap i j k h h₁ q ((Abelian.inverseImage e).obj F) ≫
        (Derived.higherDirectImage j q).map
          ((Abelian.inverseImageCompIso k e).inv.app F) := sorry

/-- For a tower of cartesian squares, the canonical outer derived base-change component is an
isomorphism when the two successive canonical components are isomorphisms. -/
theorem etaleDerivedBaseChange_comp_isIso
    {W Z X Y S T : Scheme.{u}}
    (i : W ⟶ X) (j : Z ⟶ W) (k : Z ⟶ Y) (f : X ⟶ S)
    (h : Y ⟶ X) (e : Y ⟶ T) (g : T ⟶ S)
    (h₁ : IsPullback j k i h) (h₀ : IsPullback h e f g)
    (K : DerivedCategory (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}))
    [IsIso (derivedMap f h e g h₀ K)]
    [IsIso (derivedMap i j k h h₁ ((Derived.inverseImage e).obj K))] :
    IsIso (derivedMap (i ≫ f) j (k ≫ e) g (h₁.paste_vert h₀) K) := sorry

/-- For a tower of cartesian squares, the canonical outer degreewise higher-direct-image component
is an isomorphism when the two successive canonical components are isomorphisms. -/
theorem etaleHigherDirectImageBaseChange_comp_isIso
    {W Z X Y S T : Scheme.{u}}
    (i : W ⟶ X) (j : Z ⟶ W) (k : Z ⟶ Y) (f : X ⟶ S)
    (h : Y ⟶ X) (e : Y ⟶ T) (g : T ⟶ S)
    (h₁ : IsPullback j k i h) (h₀ : IsPullback h e f g) (q : ℕ)
    (F : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})
    [IsIso (higherMap f h e g h₀ q F)]
    [IsIso (higherMap i j k h h₁ q ((Abelian.inverseImage e).obj F))] :
    IsIso (higherMap (i ≫ f) j (k ≫ e) g (h₁.paste_vert h₀) q F) := sorry

end AlgebraicGeometry.Scheme.Etale.BaseChange

end
