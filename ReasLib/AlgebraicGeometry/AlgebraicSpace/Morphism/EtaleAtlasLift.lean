module

public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import Mathlib.CategoryTheory.MorphismProperty.Representable
public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import Mathlib.CategoryTheory.Sites.Over
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Presentation

/-!
# Lifting étale atlases along morphisms of algebraic spaces

Given a morphism `a : F ⟶ G` of algebraic spaces and a representable étale atlas of `G`,
the represented fibre product of that atlas with an atlas of `F` produces a scheme over `S`
together with comparison maps forming a commutative square.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits MorphismProperty
open Functor.relativelyRepresentable

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {F G : AlgebraicSpace S} (a : F ⟶ G)
variable {W V : Over S} (pW : yoneda.obj W ⟶ F.functorOfPoints)
variable (q : yoneda.obj V ⟶ G.functorOfPoints)
variable (hq : (over (@Etale)).presheaf q)

/-- The represented fibre product `U = W ×_G V` of an atlas `pW : W ⟶ F` with a
representable étale atlas `q : V ⟶ G`, along the morphism `a : F ⟶ G`. -/
def liftEtaleAtlas : Over S :=
  hq.rep.pullback (pW ≫ a)

/-- The comparison morphism `α : U ⟶ V` in the lift of `q` along `a`. -/
def liftEtaleAtlas_fst : liftEtaleAtlas a pW q hq ⟶ V :=
  hq.rep.fst' (pW ≫ a)

/-- The base-change projection `U ⟶ W` of `q` along `pW ≫ a`. -/
def liftEtaleAtlas_snd : liftEtaleAtlas a pW q hq ⟶ W :=
  hq.rep.snd (pW ≫ a)

/-- The lifted atlas `p : U ⟶ F`, obtained by composing `U ⟶ W` with `pW`. -/
def liftEtaleAtlas_map : yoneda.obj (liftEtaleAtlas a pW q hq) ⟶ F.functorOfPoints :=
  yoneda.map (liftEtaleAtlas_snd a pW q hq) ≫ pW

/-- The lifted square commutes: `p ≫ a = yoneda.map α ≫ q`. -/
theorem liftEtaleAtlas_w :
    liftEtaleAtlas_map a pW q hq ≫ a =
      yoneda.map (liftEtaleAtlas_fst a pW q hq) ≫ q := sorry

/-- The represented square of `q` and `pW ≫ a` is a pullback. -/
theorem liftEtaleAtlas_isPullback :
    IsPullback (yoneda.map (liftEtaleAtlas_fst a pW q hq))
      (yoneda.map (liftEtaleAtlas_snd a pW q hq)) q (pW ≫ a) := sorry

/-- The comparison square of the lifted atlas commutes. -/
theorem liftEtaleAtlas_commSq :
    CommSq (yoneda.map (liftEtaleAtlas_fst a pW q hq))
      (liftEtaleAtlas_map a pW q hq) q a := sorry

/-- The base-change projection `U ⟶ W` is étale. -/
instance liftEtaleAtlas_snd_etale : Etale (liftEtaleAtlas_snd a pW q hq).left := sorry

/-- If `pW` is a representable étale atlas, then the lifted map `U ⟶ F` is representable and
étale. -/
theorem liftEtaleAtlas_map_etale (hpW_etale : (over (@Etale)).presheaf pW) :
    (over (@Etale)).presheaf (liftEtaleAtlas_map a pW q hq) := sorry

/-- If `pW` and `q` are étale-locally surjective, then the lifted map `U ⟶ F` is
étale-locally surjective. -/
theorem liftEtaleAtlas_map_locallySurjective
    (hpW_surj : Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) pW)
    (hq_surj : Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) q) :
    Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S)
      (liftEtaleAtlas_map a pW q hq) := sorry

/-- The constructed diagram is a commutative square whose vertical map `U ⟶ F` is a
surjective étale atlas. -/
theorem liftEtaleAtlas_spec (hpW_etale : (over (@Etale)).presheaf pW)
    (hpW_surj : Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) pW)
    (hq_surj : Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) q) :
    (over (@Etale)).presheaf (liftEtaleAtlas_map a pW q hq) ∧
      Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S)
          (liftEtaleAtlas_map a pW q hq) ∧
        liftEtaleAtlas_map a pW q hq ≫ a =
          yoneda.map (liftEtaleAtlas_fst a pW q hq) ≫ q := sorry

/-- A surjective étale scheme atlas of `G` lifts along any morphism `F ⟶ G` to a
surjective étale scheme atlas of `F` with a commuting comparison square. -/
theorem exists_etale_atlas_lift {S : Scheme.{u}} {F G : AlgebraicSpace S} (a : F ⟶ G)
    {V : Over S} (q : yoneda.obj V ⟶ G.functorOfPoints)
    (hq_etale : (over (@Etale)).presheaf q)
    (hq_surj : Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) q) :
    ∃ (U : Over S) (α : U ⟶ V) (p : yoneda.obj U ⟶ F.functorOfPoints),
      (over (@Etale)).presheaf p ∧
        Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) p ∧
          p ≫ a = yoneda.map α ≫ q := sorry

end AlgebraicGeometry.AlgebraicSpace
