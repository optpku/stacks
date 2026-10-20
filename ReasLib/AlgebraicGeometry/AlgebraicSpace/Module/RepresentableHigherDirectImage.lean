/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.HigherDirectImage.EtaleBaseChange
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Pullback.Representable
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Quasicoherent
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Surjective
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.QuasiCompact

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

/-- For a representable quasi-compact quasi-separated morphism, restriction of a higher
 direct image of a quasi-coherent module to an étale surjective scheme atlas is canonically
 isomorphic to the higher direct image of its restriction to the represented pullback. -/
def representableHigherDirectImageIso {f : X ⟶ Y} (hf : yoneda.relativelyRepresentable f)
    [QuasiCompact f] [QuasiSeparated f] {V : Over S} (g : ofOver V ⟶ Y)
    [Etale g] [Surjective g]
    [Abelian X.Modules] [Abelian Y.Modules]
    [Abelian (ofOver (hf.pullback g)).Modules]
    [Abelian (ofOver V).Modules]
    [HasInjectiveResolutions X.Modules]
    [HasInjectiveResolutions (ofOver (hf.pullback g)).Modules]
    (F : X.Modules) [F.IsQuasicoherent] (i : ℕ) :
    (restrictFunctor g).obj (higherDirectImage f F i) ≅
      higherDirectImage (representablePullbackSnd hf g)
        (restrict F (representablePullbackFst hf g)) i :=
  higherDirectImageEtaleBaseChangeIso (representablePullback_isPullback hf g) F i

/-- The represented higher-direct-image isomorphism is the étale base-change isomorphism
at the represented pullback square. -/
theorem representableHigherDirectImageIso_eq {f : X ⟶ Y}
    (hf : yoneda.relativelyRepresentable f)
    [QuasiCompact f] [QuasiSeparated f] {V : Over S} (g : ofOver V ⟶ Y)
    [Etale g] [Surjective g]
    [Abelian X.Modules] [Abelian Y.Modules]
    [Abelian (ofOver (hf.pullback g)).Modules]
    [Abelian (ofOver V).Modules]
    [HasInjectiveResolutions X.Modules]
    [HasInjectiveResolutions (ofOver (hf.pullback g)).Modules]
    (F : X.Modules) [F.IsQuasicoherent] (i : ℕ) :
    representableHigherDirectImageIso hf g F i =
      higherDirectImageEtaleBaseChangeIso (representablePullback_isPullback hf g) F i :=
  rfl

/-- The forward map of the represented higher-direct-image isomorphism is the canonical
higher-direct-image base-change comparison. -/
theorem representableHigherDirectImageIso_spec {f : X ⟶ Y}
    (hf : yoneda.relativelyRepresentable f)
    [QuasiCompact f] [QuasiSeparated f] {V : Over S} (g : ofOver V ⟶ Y)
    [Etale g] [Surjective g]
    [Abelian X.Modules] [Abelian Y.Modules]
    [Abelian (ofOver (hf.pullback g)).Modules]
    [Abelian (ofOver V).Modules]
    [HasInjectiveResolutions X.Modules]
    [HasInjectiveResolutions (ofOver (hf.pullback g)).Modules]
    (F : X.Modules) [F.IsQuasicoherent] (i : ℕ) :
    (representableHigherDirectImageIso hf g F i).hom =
      higherDirectImageEtaleBaseChangeHom (representablePullback_isPullback hf g) F i :=
  higherDirectImageEtaleBaseChangeIso_hom (representablePullback_isPullback hf g) F i

end AlgebraicGeometry.AlgebraicSpace.Modules
