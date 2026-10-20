module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.AffineEtale
import StacksCheckRecall

universe u

/- Lemma 74.5.1: let `S` be a scheme, let `X` be an algebraic space over `S`, and
let `F` be a presheaf of `𝒪_X`-modules on `X_affine,étale`. The following are
equivalent: for every morphism `U ⟶ U'` of `X_affine,étale` the map
`F(U') ⊗_{𝒪_X(U')} 𝒪_X(U) ⟶ F(U)` is an isomorphism; `F` is a quasi-coherent
module on the ringed site `(X_affine,étale, 𝒪_X)` in the sense of
`SheafOfModules.IsQuasicoherent`; and `F` corresponds to a quasi-coherent module
on `X` via the equivalence (74.5.0.1), represented by `qcRestriction X`. -/
@[stacks 0H04] #check (AlgebraicGeometry.AlgebraicSpace.AffineEtale.quasicoherent_tfae :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} {X : AlgebraicGeometry.AlgebraicSpace S}
    (F : PresheafOfModules.{u}
      (CategoryTheory.Presheaf.ringPresheafOfComm
        (AlgebraicGeometry.AlgebraicSpace.AffineEtale.commStructurePresheaf X))),
    List.TFAE [AlgebraicGeometry.AlgebraicSpace.AffineEtale.baseChangeCompatible F,
      AlgebraicGeometry.AlgebraicSpace.AffineEtale.isQuasicoherent F,
      AlgebraicGeometry.AlgebraicSpace.AffineEtale.correspondsToQuasiCoherent F])
