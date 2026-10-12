/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Extension.Cotangent.NaiveComplex

/-!
# Isomorphisms of naive cotangent complexes

Mutually inverse morphisms of algebra extensions induce an explicit isomorphism of their naive
cotangent complexes.  This file centralizes the chain-map composition argument.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v w

namespace Algebra.Extension.NaiveCotangent

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable {P Q : Algebra.Extension.{w} R S}

/-- The kernel-surjection of an extension makes scalar multiplication compatible across the
tensor factors defining its conormal module. -/
@[stacks 07BN "extension cotangent tensor compatibility"]
instance cotangentCompatibleSMul (P : Algebra.Extension.{w} R S) :
    _root_.TensorProduct.CompatibleSMul P.Ring S S P.Cotangent :=
  _root_.TensorProduct.CompatibleSMul.of_algebraMap_surjective
    S P.Cotangent P.algebraMap_surjective

/-- Scalar extension of the kernel cotangent module is canonically the lifted conormal module
used in the naive cotangent complex. -/
@[stacks 07BN "scalar-extended kernel cotangent identification"]
noncomputable def cotangentBaseChangeIso (P : Algebra.Extension.{w} R S) :
    ModuleCat.of.{max v w} S (TensorProduct P.Ring S P.ker.Cotangent) ≅
      ModuleCat.of.{max v w} S (Lift P) :=
  ((P.cotangentEquivCotangentKer.symm.baseChange P.Ring S) ≪≫ₗ
    _root_.TensorProduct.lidOfCompatibleSMul P.Ring S P.Cotangent ≪≫ₗ
    (liftEquiv P).symm).toModuleIso

/-- Chain maps induced by inverse extension morphisms compose to the identity on the source
complex. -/
theorem chainMap_hom_inv_id (f : P.Hom Q) (g : Q.Hom P)
    (hgf : g.comp f = .id P) :
    chainMap f ≫ chainMap g = 𝟙 (complex P) := sorry

/-- Chain maps induced by inverse extension morphisms compose to the identity on the target
complex. -/
theorem chainMap_inv_hom_id (f : P.Hom Q) (g : Q.Hom P)
    (hfg : f.comp g = .id Q) :
    chainMap g ≫ chainMap f = 𝟙 (complex Q) := sorry

/-- Mutually inverse morphisms of algebra extensions induce a canonical isomorphism of their
naive cotangent complexes. -/
@[stacks 07BN "naive cotangent complex isomorphism from extension morphisms"]
noncomputable def isoOfHom (f : P.Hom Q) (g : Q.Hom P)
    (hgf : g.comp f = .id P) (hfg : f.comp g = .id Q) :
    complex P ≅ complex Q where
  hom := chainMap f
  inv := chainMap g
  hom_inv_id := chainMap_hom_inv_id f g hgf
  inv_hom_id := chainMap_inv_hom_id f g hfg

/-- The forward morphism of `isoOfHom` is the chain map induced by the forward extension
morphism. -/
theorem isoOfHom_hom (f : P.Hom Q) (g : Q.Hom P)
    (hgf : g.comp f = .id P) (hfg : f.comp g = .id Q) :
    (isoOfHom f g hgf hfg).hom = chainMap f := sorry

/-- The inverse morphism of `isoOfHom` is the chain map induced by the inverse extension
morphism. -/
theorem isoOfHom_inv (f : P.Hom Q) (g : Q.Hom P)
    (hgf : g.comp f = .id P) (hfg : f.comp g = .id Q) :
    (isoOfHom f g hgf hfg).inv = chainMap g := sorry

end Algebra.Extension.NaiveCotangent
