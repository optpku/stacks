module

import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Functor.Equivalence.QuasiInverse.Adjointification

/-!
# Equivalences from faithful functors

A faithful functor with an essentially surjective quasi-inverse is an equivalence. The supplied
comparison with the identity determines explicit quasi-inverse data.
-/

@[expose] public section

universe vA uA vB uB

namespace CategoryTheory.Functor.IsEquivalence.ofFaithful

variable {A : Type uA} [Category.{vA} A]
variable {B : Type uB} [Category.{vB} B]

/-- If `F` is faithful, `G` is essentially surjective, and `G ⋙ F` is isomorphic to the identity,
then `F` is an equivalence. No additive or
exactness assumptions are needed for this categorical criterion. -/
@[stacks 019F "equivalence from a faithful functor and an essentially surjective quasi-inverse"]
theorem essSurj (F : A ⥤ B) (G : B ⥤ A)
    [F.Faithful] [G.EssSurj] (counitIso : G ⋙ F ≅ 𝟭 B) :
    F.IsEquivalence := sorry

namespace comparison

/-- The comparison identifying `G.obj (F.obj X)` with `X`, constructed using an
essential-surjectivity preimage of `X`. These components assemble into a natural isomorphism. -/
@[stacks 019F "objectwise supplied quasi-inverse comparison"]
noncomputable def app (F : A ⥤ B) (G : B ⥤ A)
    [F.Faithful] [G.EssSurj] (counitIso : G ⋙ F ≅ 𝟭 B) (X : A) :
    G.obj (F.obj X) ≅ X :=
  G.mapIso (F.mapIso (G.objObjPreimageIso X).symm) ≪≫
    G.mapIso (counitIso.app (G.objPreimage X)) ≪≫
      G.objObjPreimageIso X

/-- The quasi-inverse comparison components are natural in the source object. -/
@[stacks 019F "naturality of the supplied quasi-inverse comparison"]
theorem naturality (F : A ⥤ B) (G : B ⥤ A)
    [F.Faithful] [G.EssSurj] (counitIso : G ⋙ F ≅ 𝟭 B)
    {X Y : A} (f : X ⟶ Y) :
    G.map (F.map f) ≫ (app F G counitIso Y).hom =
      (app F G counitIso X).hom ≫ f := sorry

/-- The functorial comparison `F ⋙ G ≅ 𝟭 A` constructed from faithfulness, essential
surjectivity, and the supplied comparison `G ⋙ F ≅ 𝟭 B`. -/
@[stacks 019F "natural supplied quasi-inverse comparison"]
noncomputable def iso (F : A ⥤ B) (G : B ⥤ A)
    [F.Faithful] [G.EssSurj] (counitIso : G ⋙ F ≅ 𝟭 B) :
    F ⋙ G ≅ 𝟭 A :=
  NatIso.ofComponents (fun X ↦ app F G counitIso X)
    (fun f ↦ naturality F G counitIso f)

/-- The component of the functorial quasi-inverse comparison is the explicitly supplied
objectwise comparison. -/
@[simp, stacks 019F "component of the supplied quasi-inverse comparison"]
theorem iso.app (F : A ⥤ B) (G : B ⥤ A)
    [F.Faithful] [G.EssSurj] (counitIso : G ⋙ F ≅ 𝟭 B) (X : A) :
    (iso F G counitIso).app X = app F G counitIso X := sorry

end comparison

/-- The supplied functor `G`, together with both constructed comparison isomorphisms, is explicit
quasi-inverse data for `F`. -/
@[stacks 019F "explicit supplied quasi-inverse"]
noncomputable def quasiInverse (F : A ⥤ B) (G : B ⥤ A)
    [F.Faithful] [G.EssSurj] (counitIso : G ⋙ F ≅ 𝟭 B) :
    Functor.QuasiInverse F where
  inverse := G
  unitIso := (comparison.iso F G counitIso).symm
  counitIso := counitIso

/-- The inverse functor in the supplied quasi-inverse data is `G`. -/
@[simp, stacks 019F "inverse functor of the supplied quasi-inverse"]
theorem quasiInverse.inverse (F : A ⥤ B) (G : B ⥤ A)
    [F.Faithful] [G.EssSurj] (counitIso : G ⋙ F ≅ 𝟭 B) :
    (quasiInverse F G counitIso).inverse = G := sorry

/-- The unit of the supplied quasi-inverse data is the inverse of the constructed comparison. -/
@[simp, stacks 019F "unit of the supplied quasi-inverse"]
theorem quasiInverse.unitIso (F : A ⥤ B) (G : B ⥤ A)
    [F.Faithful] [G.EssSurj] (counitIso : G ⋙ F ≅ 𝟭 B) :
    (quasiInverse F G counitIso).unitIso =
      (comparison.iso F G counitIso).symm := sorry

/-- The counit of the supplied quasi-inverse data is the given comparison isomorphism. -/
@[simp, stacks 019F "counit of the supplied quasi-inverse"]
theorem quasiInverse.counitIso (F : A ⥤ B) (G : B ⥤ A)
    [F.Faithful] [G.EssSurj] (counitIso : G ⋙ F ≅ 𝟭 B) :
    (quasiInverse F G counitIso).counitIso = counitIso := sorry

/-- The equivalence whose forward and inverse functors are the supplied `F` and `G`. -/
@[stacks 019F "equivalence from a faithful functor and supplied quasi-inverse"]
noncomputable def equivalence (F : A ⥤ B) (G : B ⥤ A)
    [F.Faithful] [G.EssSurj] (counitIso : G ⋙ F ≅ 𝟭 B) : A ≌ B :=
  (quasiInverse F G counitIso).adjointifyUnit

/-- The forward functor of `ofFaithful.equivalence` is the supplied `F`. -/
@[simp, stacks 019F "forward functor of the supplied equivalence"]
theorem equivalence.functor (F : A ⥤ B) (G : B ⥤ A)
    [F.Faithful] [G.EssSurj] (counitIso : G ⋙ F ≅ 𝟭 B) :
    (equivalence F G counitIso).functor = F := sorry

/-- The inverse functor of `ofFaithful.equivalence` is the supplied `G`. -/
@[simp, stacks 019F "inverse functor of the supplied equivalence"]
theorem equivalence.inverse (F : A ⥤ B) (G : B ⥤ A)
    [F.Faithful] [G.EssSurj] (counitIso : G ⋙ F ≅ 𝟭 B) :
    (equivalence F G counitIso).inverse = G := sorry

/-- Under the hypotheses of `ofFaithful.essSurj`, the supplied inverse functor is also an
equivalence. -/
@[stacks 019F "supplied quasi-inverse is an equivalence"]
theorem inverse (F : A ⥤ B) (G : B ⥤ A)
    [F.Faithful] [G.EssSurj] (counitIso : G ⋙ F ≅ 𝟭 B) :
    G.IsEquivalence := sorry

end CategoryTheory.Functor.IsEquivalence.ofFaithful
