module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import ReasLib.AlgebraicGeometry.Scheme.Module.Picard.Pullback
public import ReasLib.AlgebraicGeometry.Scheme.OverField

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RigidifiedPicard

variable {k : Type u} [Field k]
variable (X : SchemeOverField k)

/-- The canonical morphism `X ×ₖ T' ⟶ X ×ₖ T` induced by `T' ⟶ T`. -/
noncomputable def baseChangeMap {T T' : Over (Spec (CommRingCat.of k))}
    (g : T' ⟶ T) : pullback X.hom T'.hom ⟶ pullback X.hom T.hom :=
  pullback.map X.hom T'.hom X.hom T.hom (𝟙 _) g.left (𝟙 _)
    (by simp) (by rw [Category.comp_id, g.w])

/-- The map `X ×ₖ T' ⟶ X ×ₖ T` commutes with the projections to `X`. -/
theorem baseChangeMap_fst {T T' : Over (Spec (CommRingCat.of k))}
    (g : T' ⟶ T) :
    baseChangeMap X g ≫ pullback.fst X.hom T.hom =
      pullback.fst X.hom T'.hom := sorry

/-- The map `X ×ₖ T' ⟶ X ×ₖ T` commutes with the projections to the varying base. -/
theorem baseChangeMap_snd {T T' : Over (Spec (CommRingCat.of k))}
    (g : T' ⟶ T) :
    baseChangeMap X g ≫ pullback.snd X.hom T.hom =
      pullback.snd X.hom T'.hom ≫ g.left := sorry

variable (σ : Spec (CommRingCat.of k) ⟶ X.left)
variable (hσ : σ ≫ X.hom = 𝟙 _)

/-- The section `T ⟶ X ×ₖ T` obtained by base change from `σ`. -/
noncomputable def baseChangeSection (T : Over (Spec (CommRingCat.of k))) :
    T.left ⟶ pullback X.hom T.hom :=
  pullback.lift (T.hom ≫ σ) (𝟙 T.left) (by simp [Category.assoc, hσ])

/-- The base-changed section followed by the projection to `X` is `T ⟶ Spec(k) ⟶ X`. -/
theorem baseChangeSection_fst (T : Over (Spec (CommRingCat.of k))) :
    baseChangeSection X σ hσ T ≫ pullback.fst X.hom T.hom = T.hom ≫ σ := sorry

/-- The base-changed section is a section of `X ×ₖ T ⟶ T`. -/
theorem baseChangeSection_snd (T : Over (Spec (CommRingCat.of k))) :
    baseChangeSection X σ hσ T ≫ pullback.snd X.hom T.hom = 𝟙 T.left := sorry

/-- Pulling a rigidified Picard class to a further base change preserves its rigidification. -/
theorem picardPullback_mem_ker {T T' : Over (Spec (CommRingCat.of k))}
    (g : T' ⟶ T)
    (x : (Scheme.Hom.picardPullback (baseChangeSection X σ hσ T)).ker) :
    Scheme.Hom.picardPullback (baseChangeMap X g) x ∈
      (Scheme.Hom.picardPullback (baseChangeSection X σ hσ T')).ker := sorry

/-- Pullback of a rigidified Picard class along a morphism of `k`-schemes. -/
noncomputable def map {T T' : Over (Spec (CommRingCat.of k))} (g : T' ⟶ T) :
    (Scheme.Hom.picardPullback (baseChangeSection X σ hσ T)).ker →
      (Scheme.Hom.picardPullback (baseChangeSection X σ hσ T')).ker :=
  fun x ↦ ⟨Scheme.Hom.picardPullback (baseChangeMap X g) x,
    picardPullback_mem_ker X σ hσ g x⟩

/-- Pullback of rigidified Picard classes along an identity morphism is the identity. -/
theorem map_id (T : (Over (Spec (CommRingCat.of k)))ᵒᵖ) :
    map X σ hσ (𝟙 T).unop = id := sorry

/-- Pullback of rigidified Picard classes is compatible with composition. -/
theorem map_comp {T T' T'' : (Over (Spec (CommRingCat.of k)))ᵒᵖ}
    (g : T ⟶ T') (g' : T' ⟶ T'') :
    map X σ hσ (g ≫ g').unop =
      Function.comp (map X σ hσ g'.unop) (map X σ hσ g.unop) := sorry

/-- The functor of Picard classes on `X ×ₖ T` whose pullback along `σ_T` is trivial. -/
noncomputable def functor :
    (Over (Spec (CommRingCat.of k)))ᵒᵖ ⥤ Type (u + 1) where
  obj T := (Scheme.Hom.picardPullback (baseChangeSection X σ hσ T.unop)).ker
  map g := TypeCat.ofHom (map X σ hσ g.unop)
  map_id T := congrArg TypeCat.ofHom (map_id X σ hσ T)
  map_comp g g' := congrArg TypeCat.ofHom (map_comp X σ hσ g g')

/-- The value of the rigidified Picard functor is the kernel of restriction along `σ_T`. -/
theorem functor_obj (T : Over (Spec (CommRingCat.of k))) :
    (functor X σ hσ).obj (op T) =
      (Scheme.Hom.picardPullback (baseChangeSection X σ hσ T)).ker := sorry

end AlgebraicGeometry.RigidifiedPicard
