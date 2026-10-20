/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Quasicoherent.EtaleLocal
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

/- Lemma 66.29.6: let `S` be a scheme. Let `X` be an algebraic space over `S`. Let `F`
be a sheaf of `𝒪_X`-modules. The following are equivalent: `F` is a quasi-coherent
`𝒪_X`-module; there exists an étale morphism `f : Y ⟶ X` of algebraic spaces over `S`
with `|f| : |Y| ⟶ |X|` surjective such that `f* F` is quasi-coherent on `Y`; there
exists a scheme `U` and a surjective étale morphism `φ : U ⟶ X` such that `φ* F` is a
quasi-coherent `𝒪_U`-module; and for every affine scheme `U` and étale morphism
`φ : U ⟶ X` the restriction `φ* F` is a quasi-coherent `𝒪_U`-module. -/
@[stacks 03M0] #check
  (AlgebraicGeometry.AlgebraicSpace.Modules.isQuasicoherent_tfae :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} (F : X.Modules),
    List.TFAE [F.IsQuasicoherent, IsQuasicoherent.existsEtale F,
      IsQuasicoherent.existsScheme F, IsQuasicoherent.forallAffine F])

end AlgebraicGeometry.AlgebraicSpace.Modules
