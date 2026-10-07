module

public import stacks_project.Chap10.Lemma_10_143_11.IdealAndCotangentMaps
import StacksCheckRecall

/-!
# Lemma 10.143.11

This support file records the kernel and square-zero ideal transport statements used to compare
the two extensions in the source diagram.  The ideal-to-kernel equivalence remains explicit data.

@stack 05YT
-/

@[expose] public section

-- Declarations moved out of `Lemma_10_143_11.lean` to keep the active proof file small.

open scoped TensorProduct

universe u v w x

namespace RingHom

section

variable {Aprime : Type u} {A : Type v} {Bprime : Type w} {B : Type x}
variable [CommRing Aprime] [CommRing A] [CommRing Bprime] [CommRing B]
variable (g : Aprime →+* Bprime) (qA : Aprime →+* A) (qB : Bprime →+* B) (f : A →+* B)

/-- Helper for Lemma 10.143.11: once a comparison map induces a bijection on the source and target
kernels, surjectivity of the quotient maps upgrades it to a bijection of rings. -/
lemma comparison_bijective_of_kerMap_bijective
    {C : Type*} [CommRing C] {qC : C →+* B} {φ : C →+* Bprime}
    (hSurjC : Function.Surjective qC)
    (hcomp : qB.comp φ = qC)
    (hker_bij :
      Function.Bijective
        (RingHom.kerMap φ hcomp)) :
    Function.Bijective φ := sorry

/-- Helper for Lemma 10.143.11: if the restricted kernel map becomes the identity after
transporting both kernels to a common model, then the restricted kernel map is bijective. -/
lemma kerMap_bijective_of_transport_identity
    {C : Type*} [CommRing C] {B₀ : Type*} [CommRing B₀] {B₁ : Type*} [CommRing B₁]
    {qC : C →+* B₀} {qB : B₁ →+* B₀} {φ : C →+* B₁}
    {M : Type*}
    (hcomp : qB.comp φ = qC)
    (eSrc : M ≃ ker qC) (eTgt : M ≃ ker qB)
    (htransport :
      ∀ x : M,
        eTgt.symm (RingHom.kerMap φ hcomp (eSrc x)) = x) :
    Function.Bijective (RingHom.kerMap φ hcomp) := sorry

/-- Helper for Lemma 10.143.11: an explicit kernel equality identifies the textbook ideal model
with the actual kernel subtype. -/
noncomputable def ideal_equiv_ker
    {R : Type*} [CommRing R] {S : Type*} [CommRing S]
    (q : R →+* S) (J : Ideal R) (hJ : RingHom.ker q = J) :
    J ≃ RingHom.ker q where
  toFun x := ⟨x.1, by simpa [hJ] using x.2⟩
  invFun x := ⟨x.1, by simpa [hJ] using x.2⟩
  left_inv x := by
    rfl
  right_inv x := by
    rfl

/-- Helper for Lemma 10.143.11: after identifying `ker qC` and `ker qB` with the mapped ideals
`Ideal.map c I` and `Ideal.map g I`, the kernel restriction is exactly the explicit ideal map
transporting `φ`. -/
lemma kerMap_eq_mapMap
    {R : Type*} [CommRing R] {C : Type*} [CommRing C]
    {B₀ : Type*} [CommRing B₀] {B₁ : Type*} [CommRing B₁]
    {I : Ideal R} {c : R →+* C} {g : R →+* B₁}
    {qC : C →+* B₀} {qB : B₁ →+* B₀} {φ : C →+* B₁}
    (hq : qB.comp φ = qC) (hg : φ.comp c = g)
    (hSrc : RingHom.ker qC = Ideal.map c I)
    (hTgt : RingHom.ker qB = Ideal.map g I)
    (x : Ideal.map c I) :
    (ideal_equiv_ker qB (Ideal.map g I) hTgt).symm
      (RingHom.kerMap φ hq
        ((ideal_equiv_ker qC (Ideal.map c I) hSrc) x)) =
      Ideal.mapMap I φ hg x := sorry

/-- Helper for Lemma 10.143.11: the explicit textbook map `IC → J` is already surjective once
the lifted quotient map `qC : C → B` is surjective and the target kernel is square-zero. -/
lemma mapMap_surjective_of_square_zero
    {R : Type*} [CommRing R] {C : Type*} [CommRing C]
    {B₀ : Type*} [CommRing B₀] {B₁ : Type*} [CommRing B₁]
    {I : Ideal R} {c : R →+* C} {g : R →+* B₁}
    {qC : C →+* B₀} {qB : B₁ →+* B₀} {φ : C →+* B₁}
    (hSurjC : Function.Surjective qC)
    (hq : qB.comp φ = qC) (hg : φ.comp c = g)
    (hSqB : (RingHom.ker qB) ^ 2 = ⊥)
    (hTgt : RingHom.ker qB = Ideal.map g I) :
    Function.Surjective (Ideal.mapMap I φ hg) := sorry

/-- Helper for Lemma 10.143.11: surjectivity on the textbook ideal comparison `IC → J`
upgrades to surjectivity of the whole comparison map `C → B'`. -/
lemma comparison_surjective_of_mapMap_surjective
    {R : Type*} [CommRing R] {C : Type*} [CommRing C]
    {B₀ : Type*} [CommRing B₀] {B₁ : Type*} [CommRing B₁]
    {I : Ideal R} {c : R →+* C} {g : R →+* B₁}
    {qC : C →+* B₀} {qB : B₁ →+* B₀} {φ : C →+* B₁}
    (hSurjC : Function.Surjective qC)
    (hq : qB.comp φ = qC) (hg : φ.comp c = g)
    (hTgt : RingHom.ker qB = Ideal.map g I)
    (hφI_surj : Function.Surjective (Ideal.mapMap I φ hg)) :
    Function.Surjective φ := sorry

/-- Helper for Lemma 10.143.11: injectivity on the textbook ideal comparison `IC → J`
upgrades to injectivity of the whole comparison map `C → B'`. -/
lemma comparison_injective_of_mapMap_injective
    {R : Type*} [CommRing R] {C : Type*} [CommRing C]
    {B₀ : Type*} [CommRing B₀] {B₁ : Type*} [CommRing B₁]
    {I : Ideal R} {c : R →+* C} {g : R →+* B₁}
    {qC : C →+* B₀} {qB : B₁ →+* B₀} {φ : C →+* B₁}
    (hq : qB.comp φ = qC) (hg : φ.comp c = g)
    (hSrc : RingHom.ker qC = Ideal.map c I)
    (hφI_inj : Function.Injective (Ideal.mapMap I φ hg)) :
    Function.Injective φ := sorry

/-- Helper for Lemma 10.143.11: once the source-faithful ideal models `IC` and `J` are identified
with a common object, the remaining kernel bijectivity is just the existing transported-identity
argument with the trivial ideal-to-kernel casts folded in. -/
lemma kerMap_bijective_of_ideal_transport_identity
    {C : Type*} [CommRing C] {B₀ : Type*} [CommRing B₀] {B₁ : Type*} [CommRing B₁]
    {qC : C →+* B₀} {qB : B₁ →+* B₀} {φ : C →+* B₁}
    {M : Type*} {JSrc : Ideal C} {JTgt : Ideal B₁}
    (hcomp : qB.comp φ = qC)
    (hSrc : RingHom.ker qC = JSrc)
    (hTgt : RingHom.ker qB = JTgt)
    (eIdealSrc : M ≃ JSrc) (eIdealTgt : M ≃ JTgt)
    (htransport :
      ∀ x : M,
        eIdealTgt.symm
          ((ideal_equiv_ker qB JTgt hTgt).symm
            (RingHom.kerMap φ hcomp
              ((eIdealSrc.trans (ideal_equiv_ker qC JSrc hSrc)) x))) = x) :
    Function.Bijective (RingHom.kerMap φ hcomp) := sorry

/-- Helper for Lemma 10.143.11: once the source and target textbook ideals are identified with a
common model on which the restricted kernel map is the identity, the whole comparison map is
bijective. -/
lemma comparison_bijective_of_ideal_transport_identity
    {R : Type*} [CommRing R] {C : Type*} [CommRing C]
    {B₀ : Type*} [CommRing B₀] {B₁ : Type*} [CommRing B₁]
    {I : Ideal R} {c : R →+* C} {g : R →+* B₁}
    {qC : C →+* B₀} {qB : B₁ →+* B₀} {φ : C →+* B₁}
    {M : Type u}
    (hSurjC : Function.Surjective qC)
    (hq : qB.comp φ = qC)
    (hSrc : RingHom.ker qC = Ideal.map c I)
    (hTgt : RingHom.ker qB = Ideal.map g I)
    (eIdealSrc : M ≃ Ideal.map c I) (eIdealTgt : M ≃ Ideal.map g I)
    (htransport :
      ∀ x : M,
        eIdealTgt.symm
          ((ideal_equiv_ker qB (Ideal.map g I) hTgt).symm
            (RingHom.kerMap φ hq
              ((eIdealSrc.trans (ideal_equiv_ker qC (Ideal.map c I) hSrc)) x))) = x) :
    Function.Bijective φ := sorry

/-- Helper for Lemma 10.143.11: if the textbook ideal comparison `IC → J` becomes the identity
after transporting both ideals to a common model, then the ideal comparison is injective. -/
lemma mapMap_injective_of_transport_identity
    {R : Type*} [CommRing R] {S : Type*} [CommRing S] {T : Type*} [CommRing T]
    {I : Ideal R} {f : R →+* S} {g : R →+* T} {φ : S →+* T}
    {M : Type*}
    (hcomp : φ.comp f = g)
    (eIdealSrc : M ≃ Ideal.map f I) (eIdealTgt : M ≃ Ideal.map g I)
    (htransport :
      ∀ x : M,
        eIdealTgt.symm (Ideal.mapMap I φ hcomp (eIdealSrc x)) = x) :
    Function.Injective (Ideal.mapMap I φ hcomp) := sorry

/-- Helper for Lemma 10.143.11: once the source and target textbook ideals are identified with a
common model on which the textbook ideal comparison is the identity, the whole comparison map is
injective. -/
lemma comparison_injective_of_ideal_transport_identity
    {R : Type*} [CommRing R] {C : Type*} [CommRing C]
    {B₀ : Type*} [CommRing B₀] {B₁ : Type*} [CommRing B₁]
    {I : Ideal R} {c : R →+* C} {g : R →+* B₁}
    {qC : C →+* B₀} {qB : B₁ →+* B₀} {φ : C →+* B₁}
    {M : Type*}
    (hq : qB.comp φ = qC) (hg : φ.comp c = g)
    (hSrc : RingHom.ker qC = Ideal.map c I)
    (eIdealSrc : M ≃ Ideal.map c I) (eIdealTgt : M ≃ Ideal.map g I)
    (htransport :
      ∀ x : M,
        eIdealTgt.symm (Ideal.mapMap I φ hg (eIdealSrc x)) = x) :
    Function.Injective φ := sorry

/-- Helper for Lemma 10.143.11: if the source and target textbook ideals are identified with any
common model on which the textbook ideal comparison is the identity, then one can rebase that
transport to the literal source ideal `Ideal.map c I`. -/
lemma rebase_ideal_transport_data_to_source
    {R : Type*} [CommRing R] {S : Type*} [CommRing S] {T : Type*} [CommRing T]
    {I : Ideal R} {f : R →+* S} {g : R →+* T} {φ : S →+* T}
    {M : Type*}
    (hcomp : φ.comp f = g)
    (eIdealSrc : M ≃ Ideal.map f I) (eIdealTgt : M ≃ Ideal.map g I)
    (htransport :
      ∀ x : M,
        eIdealTgt.symm (Ideal.mapMap I φ hcomp (eIdealSrc x)) = x) :
    ∃ eIdealTgt' : Ideal.map f I ≃ Ideal.map g I,
      ∀ x : Ideal.map f I,
        eIdealTgt'.symm (Ideal.mapMap I φ hcomp x) = x := sorry

/- Lemma 10.143.11, tag `05YT`: square-zero ideal and kernel transport support. -/
@[stacks 05YT "kernel bijectivity upgrades comparison bijectivity"]
#check @comparison_bijective_of_kerMap_bijective

@[stacks 05YT "kernel transport identity"]
#check @kerMap_bijective_of_transport_identity

@[stacks 05YT "ideal-to-kernel equivalence"]
#check @ideal_equiv_ker

@[stacks 05YT "kernel restriction agrees with ideal restriction"]
#check @kerMap_eq_mapMap

@[stacks 05YT "square-zero ideal restriction is surjective"]
#check @mapMap_surjective_of_square_zero

@[stacks 05YT "ideal surjectivity upgrades comparison surjectivity"]
#check @comparison_surjective_of_mapMap_surjective

@[stacks 05YT "ideal injectivity upgrades comparison injectivity"]
#check @comparison_injective_of_mapMap_injective

@[stacks 05YT "ideal transport identity upgrades comparison bijectivity"]
#check @comparison_bijective_of_ideal_transport_identity

@[stacks 05YT "ideal transport identity upgrades comparison injectivity"]
#check @comparison_injective_of_ideal_transport_identity

@[stacks 05YT "rebase ideal transport to the source ideal"]
#check @rebase_ideal_transport_data_to_source

end

end RingHom
