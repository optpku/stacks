/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Deformation.Perturbation.Chart
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Atlas.Input
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.EtaleAtlasLift
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.HomSmall
public import ReasLib.CategoryTheory.Sites.LocalSectionDescent

/-!
# Actual perturbations obtained on a common scheme atlas

The target atlas is pulled back along the supplied reference morphism and the supplied source
atlas. The given closed-immersion representations supply the reduced charts. The scheme-chart
perturbation is then glued in the actual target sheaf along this covering of the source.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite CategoryTheory.Limits
open AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Hom.Deformation

namespace AtlasPerturbation

variable {S : Scheme.{u}} {B X X' Y Y' : AlgebraicSpace S}
variable (iX : X ⟶ X') (iY : Y ⟶ Y') (a : X ⟶ Y) (a' : X' ⟶ Y')
variable [IsFirstOrderThickening iX] [IsFirstOrderThickening iY]
variable (sqA : CommSq a iX iY a')

/-- The target chart is the scheme already supplied by the target's atlas. -/
abbrev targetAmbient : Over S := AtlasInput.scheme Y'

/-- Pull the supplied target atlas back along the actual reference map on the source atlas. -/
def sourceAmbient : Over S :=
  liftEtaleAtlas a' (AtlasInput.map X') (AtlasInput.map Y') (AtlasInput.representableEtale Y')

/-- The actual source-cover map retains the original source-atlas point. -/
def sourceAmbientMap : ofOver (sourceAmbient a') ⟶ X' :=
  liftEtaleAtlas_map a' (AtlasInput.map X') (AtlasInput.map Y')
    (AtlasInput.representableEtale Y')

/-- The reference map between the two actual ambient schemes. -/
def ambientReference : sourceAmbient a' ⟶ targetAmbient (Y' := Y') :=
  liftEtaleAtlas_fst a' (AtlasInput.map X') (AtlasInput.map Y')
    (AtlasInput.representableEtale Y')

/-- The represented source reduction is supplied by the input closed immersion. -/
theorem sourceRep : yoneda.relativelyRepresentable iX :=
  (IsClosedImmersion.presheaf (f := iX)).rep

/-- The represented target reduction is supplied by the input closed immersion. -/
theorem targetRep : yoneda.relativelyRepresentable iY :=
  (IsClosedImmersion.presheaf (f := iY)).rep

/-- The source scheme representing the reduction of the refined ambient atlas. -/
def source : Over S := (sourceRep iX).pullback (sourceAmbientMap a')
/-- The target scheme representing the reduction of the supplied target atlas. -/
def target : Over S := (targetRep iY).pullback (AtlasInput.map Y')

/-- The closed immersion of the actual source-reduction scheme into its ambient chart. -/
def sourceImmersion : source iX a' ⟶ sourceAmbient a' :=
  (sourceRep iX).snd (sourceAmbientMap a')

/-- The corresponding actual target-reduction immersion. -/
def targetImmersion : target iY ⟶ targetAmbient (Y' := Y') :=
  (targetRep iY).snd (AtlasInput.map Y')

/-- The source-reduction chart projection to the reduced algebraic space. -/
def sourceMap : ofOver (source iX a') ⟶ X :=
  (sourceRep iX).fst (sourceAmbientMap a')

/-- The target-reduction chart projection to the reduced algebraic space. -/
def targetMap : ofOver (target iY) ⟶ Y :=
  (targetRep iY).fst (AtlasInput.map Y')

include sqA in
/-- The given reduction square puts the original source chart over the target reduction. -/
private theorem reference_restricts :
    sourceMap iX a' ≫ a ≫ iY =
      yoneda.map (sourceImmersion iX a' ≫ ambientReference a') ≫ AtlasInput.map Y' := sorry

/-- The reduced reference map is the actual lift into the input's target pullback scheme. -/
def reference : source iX a' ⟶ target iY :=
  yoneda.preimage
    (((targetRep iY).isPullback (AtlasInput.map Y')).lift
      (sourceMap iX a' ≫ a)
      (yoneda.map (sourceImmersion iX a' ≫ ambientReference a'))
      (by exact reference_restricts iX iY a a' sqA))

/-- The reduced chart map has the original prescribed algebraic-space map. -/
private theorem reducedSquare :
    CommSq (sourceMap iX a') (ofOverMap (reference iX iY a a' sqA)) a (targetMap iY) :=
  sorry

/-- The source-immersion square is the original input's represented pullback. -/
theorem sourceSquare :
    CommSq (sourceMap iX a') (ofOverMap (sourceImmersion iX a')) iX (sourceAmbientMap a') :=
  ⟨((sourceRep iX).isPullback (sourceAmbientMap a')).toCommSq.w⟩

/-- The actual two scheme maps restrict to their reduced reference map. -/
private theorem schemeSquare :
    CommSq (reference iX iY a a' sqA) (sourceImmersion iX a')
      (targetImmersion iY) (ambientReference a') := sorry

/-- First-order thickenings stay first-order on the displayed scheme source chart. -/
private theorem sourceImmersion_isFirstOrder :
    AlgebraicGeometry.IsFirstOrderThickening (sourceImmersion iX a').left := sorry

/-- The displayed target reduction has the original square-zero ideal. -/
private theorem targetImmersion_isFirstOrder :
    AlgebraicGeometry.IsFirstOrderThickening (targetImmersion iY).left := sorry

/-- The reduced target atlas is the base change of the supplied etale atlas. -/
private theorem targetMap_etale : Etale (targetMap iY) := sorry

/-- The refined source atlas is locally surjective by the supplied atlas covering properties. -/
private theorem sourceAmbientMap_isLocallySurjective :
    Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) (sourceAmbientMap a') :=
  liftEtaleAtlas_map_locallySurjective a' (AtlasInput.map X') (AtlasInput.map Y')
    (AtlasInput.representableEtale Y') (AtlasInput.locallySurjective X')
    (AtlasInput.locallySurjective Y')

variable (p : Y ⟶ B)
variable (θ : (Modules.pullback a).obj (Hom.relativeDifferentials p) ⟶ Hom.conormalSheaf iX)

/-- Apply the actual scheme perturbation to the two represented chart thickenings. -/
def perturbedReference : sourceAmbient a' ⟶ targetAmbient (Y' := Y') :=
  @Chart.perturb _ _ _ _ _ _ _ _ iX inferInstance (sourceImmersion iX a')
    (@AlgebraicGeometry.IsImmersion.instOfIsClosedImmersion _ _ _
      (by exact (sourceImmersion_isFirstOrder iX a').isClosedImmersion))
    a (reference iX iY a a' sqA)
    (sourceMap iX a') (sourceAmbientMap a') (targetMap iY) (by exact targetMap_etale iY)
    (by exact reducedSquare iX iY a a' sqA) (sourceSquare iX a') p
    (Hom.derivationOfPullback p a θ) _ (targetImmersion iY) (ambientReference a')
    (by exact sourceImmersion_isFirstOrder iX a') (by exact targetImmersion_isFirstOrder iY)
    (by exact schemeSquare iX iY a a' sqA)

/-- The actual perturbed chart map into the target algebraic space. -/
def perturbedAtlasMap : ofOver (sourceAmbient a') ⟶ Y' :=
  ofOverMap (perturbedReference iX iY a a' sqA p θ) ≫ AtlasInput.map Y'

/-- The reference and parameter descend together, so the chart perturbations agree over
each actual source point. The equalities concern their constructed scheme maps. -/
private theorem perturbedAtlasMap_fibre :
    ∀ (T : (Over S)ᵒᵖ) (s t : (yoneda.obj (sourceAmbient a')).obj T),
      (sourceAmbientMap a').app T s = (sourceAmbientMap a').app T t →
      (perturbedAtlasMap iX iY a a' sqA p θ).app T s =
        (perturbedAtlasMap iX iY a a' sqA p θ).app T t := sorry

/-- The global morphism is the target-sheaf amalgamation of the specified chart perturbations. -/
def glued : X' ⟶ Y' :=
  @Presheaf.LocalSectionDescent.descend _ _ (Scheme.etaleTopology.over S) _ _ _
    (sourceAmbientMap a') (perturbedAtlasMap iX iY a a' sqA p θ)
    (by exact sourceAmbientMap_isLocallySurjective a')
    (AlgebraicSpace.Smallness.etaleSheaf Y') (by exact perturbedAtlasMap_fibre iX iY a a' sqA p θ)

/-- On the actual source atlas, the global morphism is the constructed chart map. -/
theorem glued_on_atlas :
    sourceAmbientMap a' ≫ glued iX iY a a' sqA p θ =
      perturbedAtlasMap iX iY a a' sqA p θ :=
  @Presheaf.LocalSectionDescent.descend_fac _ _ (Scheme.etaleTopology.over S) _ _ _
    (sourceAmbientMap a') (perturbedAtlasMap iX iY a a' sqA p θ)
    (by exact sourceAmbientMap_isLocallySurjective a')
    (AlgebraicSpace.Smallness.etaleSheaf Y')
    (by exact perturbedAtlasMap_fibre iX iY a a' sqA p θ)

end AtlasPerturbation

/-- Perturb an algebraic-space morphism by a differential parameter using actual scheme
atlas maps and their target-sheaf gluing. -/
def perturbHom {S : Scheme.{u}} {B X X' Y Y' : AlgebraicSpace S}
    (iX : X ⟶ X') (iY : Y ⟶ Y') (a : X ⟶ Y) (a' : X' ⟶ Y')
    [IsFirstOrderThickening iX] [IsFirstOrderThickening iY]
    (sqA : CommSq a iX iY a') (p : Y ⟶ B)
    (θ : (Modules.pullback a).obj (Hom.relativeDifferentials p) ⟶ Hom.conormalSheaf iX) :
    X' ⟶ Y' :=
  AtlasPerturbation.glued iX iY a a' sqA p θ

end AlgebraicGeometry.AlgebraicSpace.Hom.Deformation
