/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.Groupoids.Hom.OneCell
public import stacks_project.Chap96.Definition_96_6_1_StructureSheaf

/-!
# Chaotic structure sheaf and inverse-image identification

A 1-morphism `f : X ⟶ Y` of categories fibred in groupoids over `(Sch/S)_fppf`
satisfies `toFunctor f ⋙ Y.p = X.p`. Combined with `𝒪 = p⁻¹ 𝒪` this yields
`f⁻¹ 𝒪_Y = 𝒪_X` as ring presheaves. The chaotic rebundle of `𝒪_X` is the site
used to form the direct image of presheaves of modules.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Functor Opposite
open FiberedCategoryOver.Groupoids

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}}

/-- The structure sheaf `𝒪_X`, rebundled as a sheaf for the chaotic topology on
the total category of `X`. -/
def chaoticStructureSheaf (X : GroupoidsOver S) :
    Sheaf (⊥ : GrothendieckTopology X.total) RingCat.{u} :=
  ⟨(structureSheaf X).obj, Presheaf.isSheaf_bot _⟩

/-- The underlying ring presheaf of `chaoticStructureSheaf X` is `𝒪_X`. -/
theorem chaoticStructureSheaf_obj (X : GroupoidsOver S) :
    (chaoticStructureSheaf X).obj = (structureSheaf X).obj := sorry

/-- The chaotic ringed site of `X`, with the same underlying ring presheaf as
`𝒪_X`. -/
abbrev chaoticRingedSite (X : GroupoidsOver S) : RingedSite :=
  RingedSite.ofRingSheaf ⊥ (chaoticStructureSheaf X)

/-- The structure sheaf of `chaoticRingedSite X` is `chaoticStructureSheaf X`. -/
theorem chaoticRingedSite_structureSheaf (X : GroupoidsOver S) :
    (chaoticRingedSite X).structureSheaf = chaoticStructureSheaf X := sorry

/-- Unfolding of `𝒪_X = p⁻¹ 𝒪` as precomposition with `X.p.op`. -/
def structureSheafToBig (X : GroupoidsOver S) :
    (structureSheaf X).obj ≅
      X.p.op ⋙ (StandardTopology.Big.structureSheaf .fppf S).obj :=
  (X.p.sheafPushforwardContinuousCompSheafToPresheafIso RingCat.{u}
      (inheritedFppfTopology X) (Scheme.fppfTopology.over S)).app
    (StandardTopology.Big.structureSheaf .fppf S)

/-- Opposite of the commuting triangle `toFunctor f ⋙ Y.p ≅ X.p`. -/
def structureSheafInverseImageIsoOp {X Y : GroupoidsOver S} (f : X ⟶ Y) :
    (toFunctor f ⋙ Y.p).op ≅ X.p.op :=
  NatIso.op (commIso f).symm

/-- Reassociation `(toFunctor f).op ⋙ Y.p.op = (toFunctor f ⋙ Y.p).op`. -/
def structureSheafInverseImageIsoOpComp {X Y : GroupoidsOver S} (f : X ⟶ Y) :
    (toFunctor f).op ⋙ Y.p.op ≅ (toFunctor f ⋙ Y.p).op :=
  ((toFunctor f).opComp Y.p).symm

/-- The identification `f⁻¹ 𝒪_Y = 𝒪_X` of ring presheaves, from the commuting
triangle `toFunctor f ⋙ Y.p = X.p` and the definition `𝒪 = p⁻¹ 𝒪`. -/
def structureSheafInverseImageIso {X Y : GroupoidsOver S} (f : X ⟶ Y) :
    (toFunctor f).op ⋙ (structureSheaf Y).obj ≅ (structureSheaf X).obj :=
  isoWhiskerLeft (toFunctor f).op (structureSheafToBig Y) ≪≫
    isoWhiskerRight (structureSheafInverseImageIsoOpComp f)
      (StandardTopology.Big.structureSheaf .fppf S).obj ≪≫
    isoWhiskerRight (structureSheafInverseImageIsoOp f)
      (StandardTopology.Big.structureSheaf .fppf S).obj ≪≫
    (structureSheafToBig X).symm

/-- At an object `x` of `X`, the component of `structureSheafInverseImageIso f`
identifies `𝒪_Y((toFunctor f).obj x)` with `𝒪_X(x)`. -/
theorem structureSheafInverseImageIso_hom_app {X Y : GroupoidsOver S}
    (f : X ⟶ Y) (x : X.total) :
    ((toFunctor f).op ⋙ (structureSheaf Y).obj).obj (op x) =
      (structureSheaf X).obj.obj (op x) := sorry

end AlgebraicGeometry.GroupoidsOver
