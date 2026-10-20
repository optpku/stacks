module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.TangentSpace.Differentials

/-!
# Maps on relative tangent spaces

This file defines the maps on relative cotangent and tangent spaces induced by
a morphism of schemes over a common base.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- A morphism of schemes over a common base induces a map on relative Kähler
differentials at each point. -/
noncomputable def relativeCotangentMapAt
    {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S) (x : X) :
    -- Local instance justification (defeq pin): restrict the source cotangent module along
    -- the stalk map through which the induced differential map is linear.
    let _ : Module (Y.presheaf.stalk (f x))
        (CommRingCat.KaehlerDifferential ((f ≫ g).stalkMap x)) :=
      Module.compHom _ (f.stalkMap x).hom
    CommRingCat.KaehlerDifferential (g.stalkMap (f x)) →ₗ[Y.presheaf.stalk (f x)]
      CommRingCat.KaehlerDifferential ((f ≫ g).stalkMap x) :=
  ModuleCat.Hom.hom <|
    @CommRingCat.KaehlerDifferential.map
      (S.presheaf.stalk ((f ≫ g) x))
      (Y.presheaf.stalk (f x))
      (S.presheaf.stalk ((f ≫ g) x))
      (X.presheaf.stalk x)
      (g.stalkMap (f x))
      ((f ≫ g).stalkMap x)
      (𝟙 _)
      (f.stalkMap x)
      (by rw [Category.id_comp, stalkMap_comp]; rfl)

/-- If the induced residue-field map at a point is bijective, a morphism of schemes over a
common base induces a linear map on relative tangent spaces. -/
noncomputable def relativeTangentMapAt
    {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S) (x : X)
    (hκ : Function.Bijective (Scheme.Hom.residueFieldMap f x).hom) :
    -- Local instance justification (noncanonical choice): restrict the source tangent-space
    -- action along the residue-field equivalence specified by the explicit hypothesis `hκ`.
    let _ : Module (Y.residueField (f x)) (tangentSpaceAt (f ≫ g) x) :=
      Module.compHom (tangentSpaceAt (f ≫ g) x)
        (RingEquiv.ofBijective (Scheme.Hom.residueFieldMap f x).hom hκ).toRingHom
    tangentSpaceAt (f ≫ g) x →ₗ[Y.residueField (f x)] tangentSpaceAt g (f x) :=
  let eκ := RingEquiv.ofBijective (Scheme.Hom.residueFieldMap f x).hom hκ
  -- Local instance justification (noncanonical choice): use the residue-field equivalence
  -- specified by `hκ` to restrict scalars on the source tangent space.
  let _ : Module (Y.residueField (f x)) (tangentSpaceAt (f ≫ g) x) :=
    Module.compHom (tangentSpaceAt (f ≫ g) x) eκ.toRingHom
  -- Local instance justification (defeq pin): use the target stalk algebra defining the
  -- codomain relative tangent space.
  let _ : Algebra (S.presheaf.stalk (g (f x))) (Y.presheaf.stalk (f x)) :=
    (g.stalkMap (f x)).hom.toAlgebra
  -- Local instance justification (defeq pin): use the target residue algebra defining the
  -- codomain relative tangent space.
  let _ : Algebra (Y.presheaf.stalk (f x)) (Y.residueField (f x)) :=
    (Y.residue (f x)).hom.toAlgebra
  -- Local instance justification (defeq pin): use the composite target-stalk action defining
  -- the codomain relative tangent space.
  let _ : Algebra (S.presheaf.stalk (g (f x))) (Y.residueField (f x)) :=
    ((Y.residue (f x)).hom.comp (g.stalkMap (f x)).hom).toAlgebra
  { toFun := fun D ↦
      { toFun := fun a ↦ eκ.symm (D ((f.stalkMap x).hom a))
        map_add' := sorry
        map_smul' := sorry
        map_one_eq_zero' := sorry
        leibniz' := sorry }
    map_add' := sorry
    map_smul' := sorry }

/-- Evaluating the induced tangent map restricts a tangent vector along the stalk map and
transports its value through the inverse residue-field equivalence. -/
theorem relativeTangentMapAt_apply
    {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S) (x : X)
    (hκ : Function.Bijective (Scheme.Hom.residueFieldMap f x).hom)
    (D : tangentSpaceAt (f ≫ g) x) (a : Y.presheaf.stalk (f x)) :
    relativeTangentMapAt f g x hκ D a =
      (RingEquiv.ofBijective (Scheme.Hom.residueFieldMap f x).hom hκ).symm
        (D ((f.stalkMap x).hom a)) := sorry

/-- Under the canonical identification of relative tangent spaces with linear duals of Kähler
differentials, the induced tangent map is pointwise dual to the induced cotangent map. -/
theorem relativeTangentMapAt_dual
    {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S) (x : X)
    (hκ : Function.Bijective (Scheme.Hom.residueFieldMap f x).hom)
    (D : tangentSpaceAt (f ≫ g) x)
    (ω : CommRingCat.KaehlerDifferential (g.stalkMap (f x))) :
    relativeTangentSpaceLinearDual g (f x) (relativeTangentMapAt f g x hκ D) ω =
      (RingEquiv.ofBijective (Scheme.Hom.residueFieldMap f x).hom hκ).symm
        (relativeTangentSpaceLinearDual (f ≫ g) x D
          (relativeCotangentMapAt f g x ω)) := sorry

end AlgebraicGeometry.Scheme.Hom
