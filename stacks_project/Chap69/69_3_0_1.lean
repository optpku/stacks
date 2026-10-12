/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap67.«67_11_1_1»
public import stacks_project.Chap69.«69_3_0_1_Comparison»
public import stacks_project.Chap69.«69_3_0_1_HigherDirectImage»

/-!
# Representable higher direct images of quasi-coherent modules

For a representable quasi-compact quasi-separated morphism of algebraic spaces, restriction of
`R^i f_* F` to an étale scheme atlas of the target agrees with the higher direct image of the
restricted module along the base-changed morphism of schemes.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules CategoryTheory.Limits

noncomputable section

universe u

-- Local instance justification (defeq pin): `HasInjectiveResolutions` and `higherDirectImage` pin the Abelian-induced `Preadditive`/`HasZeroMorphisms` instances for defeq of `representableHigherDirectImageIso`.
attribute [local instance 2000] Abelian.toPreadditive Preadditive.preadditiveHasZeroMorphisms

namespace AlgebraicGeometry.AlgebraicSpace.Modules

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S}

/-- 69.3.0.1: Let `f : X ⟶ Y` be a representable, quasi-compact, and quasi-separated morphism of
algebraic spaces over `S`. Let `V` be a scheme and `V ⟶ Y` an étale surjective morphism, write
`U = V ×_Y X` with base change `f' : U ⟶ V`. Then for any quasi-coherent `𝒪_X`-module `F` there
is a canonical identification `R^i f'_*(F|_U) ≅ (R^i f_* F)|_V` of sheaves of modules on
`V_étale`. -/
@[stacks 071Z]
def representableHigherDirectImageIso {f : X ⟶ Y} (hf : yoneda.relativelyRepresentable f)
    [QuasiCompact f] [QuasiSeparated f] {V : Over S} (g : ofOver V ⟶ Y)
    [Etale g] [Surjective g] [Etale (representablePullbackFst hf g)]
    [Abelian X.Modules] [Abelian Y.Modules]
    [Abelian (ofOver (hf.pullback (yonedaHomOf g))).Modules]
    [Abelian (ofOver V).Modules]
    [HasInjectiveResolutions X.Modules]
    [HasInjectiveResolutions (ofOver (hf.pullback (yonedaHomOf g))).Modules]
    (F : X.Modules) [F.IsQuasicoherent] (i : ℕ) :
    (restrictFunctor g).obj (higherDirectImage f F i) ≅
      higherDirectImage (representablePullbackSnd hf g)
        (restrict F (representablePullbackFst hf g)) i :=
  higherDirectImageEtaleBaseChangeIso (representablePullback_isPullback hf g) F i

/-- The source-facing identification is the general étale cartesian comparison at the represented
pullback square of `f` along `g`. -/
theorem representableHigherDirectImageIso_eq {f : X ⟶ Y}
    (hf : yoneda.relativelyRepresentable f)
    [QuasiCompact f] [QuasiSeparated f] {V : Over S} (g : ofOver V ⟶ Y)
    [Etale g] [Surjective g] [Etale (representablePullbackFst hf g)]
    [Abelian X.Modules] [Abelian Y.Modules]
    [Abelian (ofOver (hf.pullback (yonedaHomOf g))).Modules]
    [Abelian (ofOver V).Modules]
    [HasInjectiveResolutions X.Modules]
    [HasInjectiveResolutions (ofOver (hf.pullback (yonedaHomOf g))).Modules]
    (F : X.Modules) [F.IsQuasicoherent] (i : ℕ) :
    representableHigherDirectImageIso hf g F i =
      higherDirectImageEtaleBaseChangeIso (representablePullback_isPullback hf g) F i :=
  rfl

/-- Both sides of the source identification are étale restriction and higher direct image of
`F`. -/
theorem representableHigherDirectImageIso_spec {f : X ⟶ Y}
    (hf : yoneda.relativelyRepresentable f)
    [QuasiCompact f] [QuasiSeparated f] {V : Over S} (g : ofOver V ⟶ Y)
    [Etale g] [Surjective g] [Etale (representablePullbackFst hf g)]
    [Abelian X.Modules] [Abelian Y.Modules]
    [Abelian (ofOver (hf.pullback (yonedaHomOf g))).Modules]
    [Abelian (ofOver V).Modules]
    [HasInjectiveResolutions X.Modules]
    [HasInjectiveResolutions (ofOver (hf.pullback (yonedaHomOf g))).Modules]
    (F : X.Modules) [F.IsQuasicoherent] (i : ℕ) :
    (representableHigherDirectImageIso hf g F i).hom =
      higherDirectImageEtaleBaseChangeHom (representablePullback_isPullback hf g) F i :=
  rfl

end AlgebraicGeometry.AlgebraicSpace.Modules
