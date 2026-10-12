/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.CommSq
public import Mathlib.CategoryTheory.Sites.Subcanonical
public import Mathlib.RingTheory.LaurentSeries
public import Mathlib.RingTheory.PowerSeries.Basic
public import stacks_project.Chap65.Example_65_14_2_Space

/-!
# The power-series valuative square of the Galois twist

This module records the solid square `Spec(k⸨X⸩) ⟶ X` over `Spec(k⟦X⟧) ⟶ 𝔸¹_k`
for the Galois twist of the doubled-origin line, together with the monomorphism
`Spec(k') ⟶ X` above the origin.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits Opposite
open scoped PowerSeries LaurentSeries

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.NonrepresentableDescent

/-- The structure morphism `Spec(k⟦X⟧) ⟶ 𝔸¹_k` induced by `k[x] → k⟦X⟧`. -/
def powerSeriesHom (k : Type u) [Field k] :
    Spec (CommRingCat.of (PowerSeries k)) ⟶ base k :=
  Spec.map (CommRingCat.ofHom (algebraMap (Polynomial k) (PowerSeries k)))

/-- `powerSeriesHom` is `Spec` of the algebra map `k[x] → k⟦X⟧`. -/
theorem powerSeriesHom_eq (k : Type u) [Field k] :
    powerSeriesHom k =
      Spec.map (CommRingCat.ofHom (algebraMap (Polynomial k) (PowerSeries k))) :=
  sorry

/-- `Spec(k⟦X⟧)` as a scheme over `𝔸¹_k`. -/
def powerSeriesOver (k : Type u) [Field k] : Over (base k) :=
  Over.mk (powerSeriesHom k)

/-- `powerSeriesOver` is classified by `powerSeriesHom`. -/
theorem powerSeriesOver_eq (k : Type u) [Field k] :
    powerSeriesOver k = Over.mk (powerSeriesHom k) := sorry

/-- The structure morphism of `powerSeriesOver` is `powerSeriesHom`. -/
theorem powerSeriesOver_hom (k : Type u) [Field k] :
    (powerSeriesOver k).hom = powerSeriesHom k := sorry

/-- The unique morphism `Spec(k⟦X⟧) ⟶ 𝔸¹_k` in `Over 𝔸¹_k`. -/
def powerSeriesToBase (k : Type u) [Field k] : powerSeriesOver k ⟶ baseAsOver k :=
  toBaseAsOver k (powerSeriesOver k)

/-- `powerSeriesToBase` is the unique map into `S` over `S`. -/
theorem powerSeriesToBase_eq (k : Type u) [Field k] :
    powerSeriesToBase k = toBaseAsOver k (powerSeriesOver k) := sorry

/-- The vertical morphism `Spec(k⸨X⸩) ⟶ Spec(k⟦X⟧)` induced by `k⟦X⟧ → k⸨X⸩`. -/
def verticalHom (k : Type u) [Field k] :
    Spec (CommRingCat.of (LaurentSeries k)) ⟶ Spec (CommRingCat.of (PowerSeries k)) :=
  Spec.map (CommRingCat.ofHom (algebraMap (PowerSeries k) (LaurentSeries k)))

/-- `verticalHom` is `Spec` of the algebra map `k⟦X⟧ → k⸨X⸩`. -/
theorem verticalHom_eq (k : Type u) [Field k] :
    verticalHom k =
      Spec.map (CommRingCat.ofHom (algebraMap (PowerSeries k) (LaurentSeries k))) :=
  sorry

/-- `Spec(k⸨X⸩)` as a scheme over `𝔸¹_k`, via `Spec(k⟦X⟧)`. -/
def laurentOver (k : Type u) [Field k] : Over (base k) :=
  Over.mk (verticalHom k ≫ (powerSeriesOver k).hom)

/-- `laurentOver` is classified by the composite through `Spec(k⟦X⟧)`. -/
theorem laurentOver_eq (k : Type u) [Field k] :
    laurentOver k = Over.mk (verticalHom k ≫ (powerSeriesOver k).hom) := sorry

/-- The structure morphism of `laurentOver` factors through `powerSeriesHom`. -/
theorem laurentOver_hom (k : Type u) [Field k] :
    (laurentOver k).hom = verticalHom k ≫ (powerSeriesOver k).hom := sorry

/-- The vertical arrow `Spec(k⸨X⸩) ⟶ Spec(k⟦X⟧)` of the valuative square, as a
morphism over `𝔸¹_k`. -/
def vertical (k : Type u) [Field k] : laurentOver k ⟶ powerSeriesOver k :=
  Over.homMk (verticalHom k) rfl

/-- The underlying scheme morphism of `vertical` is `verticalHom`. -/
theorem vertical_left (k : Type u) [Field k] : (vertical k).left = verticalHom k := sorry

/-- The image of `Spec(k⸨X⸩) ⟶ 𝔸¹_k` lands in the punctured open `D(x)`. -/
theorem laurent_range_subset_punctured (k : Type u) [Field k] :
    Set.range (fun x : (laurentOver k).left ↦ (laurentOver k).hom x) ⊆
      basePuncturedOpen k :=
  sorry

/-- The unique section of `π` over `Spec(k⸨X⸩)`, obtained by inverting `π` on the
punctured locus. -/
def laurentSection (k k' : Type u) [Field k] [Field k'] [Algebra k k'] [IsGalois k k']
    (hdeg : Module.finrank k k' = 2) :
    (sheafOfPoints k k' hdeg).obj.obj (Opposite.op (laurentOver k)) :=
  Function.surjInv
    (isIso_over_punctured k k' hdeg (laurentOver k) (laurent_range_subset_punctured k)).2
    (ULift.up.{u + 1} (toBaseAsOver k (laurentOver k)))

/-- The section `laurentSection` is the preimage of the unique map into `S`. -/
theorem laurentSection_spec (k k' : Type u) [Field k] [Field k'] [Algebra k k']
    [IsGalois k k'] (hdeg : Module.finrank k k' = 2) :
    (structureHom k k' hdeg).hom.app (Opposite.op (laurentOver k))
        (laurentSection k k' hdeg) =
      ULift.up.{u + 1} (toBaseAsOver k (laurentOver k)) :=
  sorry

/-- The solid top arrow `Spec(k⸨X⸩) ⟶ X` of the valuative square. -/
def laurentToSpace (k k' : Type u) [Field k] [Field k'] [Algebra k k'] [IsGalois k k']
    (hdeg : Module.finrank k k' = 2) :
    (Scheme.fppfTopology.over (base k)).uliftYoneda.{u + 1}.obj (laurentOver k) ⟶
      sheafOfPoints k k' hdeg :=
  (Scheme.fppfTopology.over (base k)).uliftYonedaEquiv.symm (laurentSection k k' hdeg)

/-- `laurentToSpace` is the Yoneda transpose of `laurentSection`. -/
theorem laurentToSpace_eq (k k' : Type u) [Field k] [Field k'] [Algebra k k']
    [IsGalois k k'] (hdeg : Module.finrank k k' = 2) :
    laurentToSpace k k' hdeg =
      (Scheme.fppfTopology.over (base k)).uliftYonedaEquiv.symm
        (laurentSection k k' hdeg) :=
  sorry

/-- The top arrow of the valuative square composes with `π` to the structure
morphism of `Spec(k⸨X⸩)`. -/
theorem laurentToSpace_comp_structureHom (k k' : Type u) [Field k] [Field k']
    [Algebra k k'] [IsGalois k k'] (hdeg : Module.finrank k k' = 2) :
    laurentToSpace k k' hdeg ≫ structureHom k k' hdeg =
      (Scheme.fppfTopology.over (base k)).uliftYoneda.{u + 1}.map
        (toBaseAsOver k (laurentOver k)) :=
  sorry

/-- The solid valuative square `Spec(k⸨X⸩) ⟶ X` over `Spec(k⟦X⟧) ⟶ 𝔸¹_k`. -/
theorem valuativeCommSq (k k' : Type u) [Field k] [Field k'] [Algebra k k'] [IsGalois k k']
    (hdeg : Module.finrank k k' = 2) :
    CommSq (laurentToSpace k k' hdeg)
      ((Scheme.fppfTopology.over (base k)).uliftYoneda.{u + 1}.map (vertical k))
      (structureHom k k' hdeg)
      ((Scheme.fppfTopology.over (base k)).uliftYoneda.{u + 1}.map (powerSeriesToBase k)) :=
  sorry

/-- There is no dotted lift `Spec(k⟦X⟧) ⟶ X` filling `valuativeCommSq`. -/
theorem not_hasLift (k k' : Type u) [Field k] [Field k'] [Algebra k k'] [IsGalois k k']
    (hdeg : Module.finrank k k' = 2) :
    ¬ (valuativeCommSq k k' hdeg).HasLift := sorry

/-- The origin `Spec(k') ⟶ U` as a morphism over `𝔸¹_k`. -/
def originToCover (k k' : Type u) [Field k] [Field k'] [Algebra k k'] :
    originOver k k' ⟶ cover k k' :=
  Over.homMk (originHom k k') rfl

/-- The underlying scheme morphism of `originToCover` is `originHom`. -/
theorem originToCover_left (k k' : Type u) [Field k] [Field k'] [Algebra k k'] :
    (originToCover k k').left = originHom k k' := sorry

/-- The unique point of `X` above `0 ∈ 𝔸¹_k`, as a morphism `Spec(k') ⟶ X`. -/
def originToSpace (k k' : Type u) [Field k] [Field k'] [Algebra k k'] [IsGalois k k']
    (hdeg : Module.finrank k k' = 2) :
    (Scheme.fppfTopology.over (base k)).uliftYoneda.{u + 1}.obj (originOver k k') ⟶
      sheafOfPoints k k' hdeg :=
  (Scheme.fppfTopology.over (base k)).uliftYoneda.{u + 1}.map (originToCover k k') ≫
    atlas k k' hdeg

/-- `originToSpace` is the atlas composite of the origin of `U`. -/
theorem originToSpace_eq (k k' : Type u) [Field k] [Field k'] [Algebra k k']
    [IsGalois k k'] (hdeg : Module.finrank k k' = 2) :
    originToSpace k k' hdeg =
      (Scheme.fppfTopology.over (base k)).uliftYoneda.{u + 1}.map (originToCover k k') ≫
        atlas k k' hdeg :=
  sorry

/-- The unique point of `X` above `0` is a monomorphism `Spec(k') ⟶ X`. -/
instance mono_originToSpace (k k' : Type u) [Field k] [Field k'] [Algebra k k']
    [IsGalois k k'] (hdeg : Module.finrank k k' = 2) :
    Mono (originToSpace k k' hdeg) := sorry

end AlgebraicGeometry.AlgebraicSpace.NonrepresentableDescent
