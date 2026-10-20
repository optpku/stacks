module

public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.RingTheory.Extension.Cotangent.Basic
public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.RingTheory.RingHomProperties
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Extension.Generators.KoszulRegular

@[expose] public section

open scoped TensorProduct

/-!
# Local Complete Intersection Ring Homomorphisms

This leaf owns the presentation-theoretic local-complete-intersection property
of an arbitrary commutative ring homomorphism.

@stack 07CZ
@stack 07D0
-/

universe u v w

namespace RingHom

noncomputable section

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B]

/-- Polynomial generators for a ring homomorphism, using the canonical algebra structure induced
by the map. This is the map-first adapter to mathlib's `Algebra.Generators`. -/
@[stacks 07D0 "polynomial presentation of a ring homomorphism"]
abbrev Generators (f : A →+* B) (ι : Type w) : Type (max u v w) :=
  @Algebra.Generators A B ι _ _ f.toAlgebra

namespace Generators

/-- The kernel ideal of a polynomial presentation of a ring homomorphism. -/
@[stacks 07CZ "kernel of a polynomial presentation"]
noncomputable abbrev ker {f : A →+* B} {ι : Type w} (P : f.Generators ι) :
    Ideal (MvPolynomial ι A) :=
  @Algebra.Generators.ker A B ι _ _ f.toAlgebra P

/-- A polynomial presentation of a ring homomorphism is Koszul-regular when its kernel is a
Koszul-regular ideal. -/
@[stacks 07CZ "Koszul-regular polynomial presentation"]
def IsKoszulRegular {f : A →+* B} {ι : Type w} (P : f.Generators ι) : Prop :=
  P.ker.IsKoszulRegularIdeal

end Generators

/-- A ring map is a local complete intersection when one finite polynomial
presentation has Koszul-regular kernel. -/
@[stacks 07D0 "local complete intersection ring maps"]
class IsLocalCompleteIntersection (f : A →+* B) : Prop where
  /-- A finite polynomial presentation whose kernel is Koszul-regular. -/
  exists_generators_ker_isKoszulRegular :
    ∃ n : ℕ, ∃ P : f.Generators (Fin n), P.IsKoszulRegular

namespace IsLocalCompleteIntersection

/-- A map is a local complete intersection exactly when its canonical
`f.toAlgebra` structure admits a finite Koszul-regular presentation. -/
@[stacks 07D0 "finite-presentation criterion for local complete-intersection maps"]
theorem iff_exists_koszulRegularPresentation (f : A →+* B) :
    f.IsLocalCompleteIntersection ↔
      ∃ n : ℕ, ∃ P : f.Generators (Fin n), P.IsKoszulRegular := sorry

/-- A short source-independent projection of the finite polynomial presentation carried by an
local complete-intersection map. -/
@[stacks 07D0 "finite polynomial presentation of a local complete-intersection map"]
theorem exists_presentation {f : A →+* B} (h : f.IsLocalCompleteIntersection) :
    ∃ n : ℕ, ∃ P : f.Generators (Fin n), P.IsKoszulRegular := sorry

/-- Build a local complete-intersection ring map from a finite polynomial presentation with
Koszul-regular kernel. -/
@[stacks 07D0 "construction from a Koszul-regular finite presentation"]
theorem of_presentation {f : A →+* B}
    (h : ∃ n : ℕ, ∃ P : f.Generators (Fin n), P.IsKoszulRegular) :
    f.IsLocalCompleteIntersection := sorry

/-- Composition of local-complete-intersection ring maps is again a local-complete-intersection
ring map. -/
@[stacks 07D0 "composition of local complete-intersection ring maps"]
theorem comp {C : Type w} [CommRing C] (f : A →+* B) (g : B →+* C)
    (hf : f.IsLocalCompleteIntersection) (hg : g.IsLocalCompleteIntersection) :
    (g.comp f).IsLocalCompleteIntersection := sorry

/-- A local-complete-intersection map remains so after postcomposition by a ring equivalence. -/
@[stacks 07D0 "target-equivalence invariance of local complete-intersection maps"]
theorem comp_ringEquiv {C : Type w} [CommRing C] (f : A →+* B) (e : B ≃+* C)
    (hf : f.IsLocalCompleteIntersection) :
    (e.toRingHom.comp f).IsLocalCompleteIntersection := sorry

/-- A local-complete-intersection map remains so after precomposition by a ring equivalence. -/
@[stacks 07D0 "source-equivalence invariance of local complete-intersection maps"]
theorem ringEquiv_comp {C : Type w} [CommRing C] (e : C ≃+* A) (f : A →+* B)
    (hf : f.IsLocalCompleteIntersection) :
    (f.comp e.toRingHom).IsLocalCompleteIntersection := sorry

/-- The local-complete-intersection property respects ring equivalences on either side. -/
@[stacks 07D0 "ring-equivalence invariance of local complete-intersection maps"]
theorem respectsIso : RingHom.RespectsIso @IsLocalCompleteIntersection := sorry

/-- Flat tensor-product base change preserves local-complete-intersection ring maps, without forcing
the source, target, and base-change algebra into one universe. -/
@[stacks 07D0 "tensor-product base change for local complete-intersection maps"]
theorem baseChange
    {R₀ S₀ R₁ : Type*} [CommRing R₀] [CommRing S₀] [CommRing R₁]
    [Algebra R₀ S₀] [Algebra R₀ R₁] [Module.Flat R₀ R₁]
    (hS : (algebraMap R₀ S₀).IsLocalCompleteIntersection) :
    (algebraMap R₁ (R₁ ⊗[R₀] S₀)).IsLocalCompleteIntersection := sorry

/-- Every finite polynomial presentation of a local complete-intersection map has
Koszul-regular kernel. -/
@[stacks 07CZ "Koszul-regular kernels of local complete-intersection presentations"]
theorem ker_isKoszulRegular {f : A →+* B} (h : f.IsLocalCompleteIntersection)
    {ι : Type w} [_root_.Finite ι] (P : f.Generators ι) : P.IsKoszulRegular := sorry

/-- A chosen finite polynomial presentation detects whether a ring map is a local complete
intersection. -/
@[stacks 07CZ "presentation criterion for local complete-intersection maps"]
theorem iff_presentation {f : A →+* B} {ι : Type w} [_root_.Finite ι]
    (P : f.Generators ι) : f.IsLocalCompleteIntersection ↔ P.IsKoszulRegular := sorry

/-- A local complete intersection ring map is of finite type. -/
@[stacks 07D0 "finite type of local complete-intersection ring maps"]
theorem finiteType {f : A →+* B} (h : f.IsLocalCompleteIntersection) : f.FiniteType := sorry

/-- A local complete-intersection ring map is of finite presentation. -/
@[stacks 07D0 "finite presentation of a local complete-intersection ring map"]
theorem finitePresentation {f : A →+* B}
    (h : f.IsLocalCompleteIntersection) : f.FinitePresentation := sorry

/-- A local-complete-intersection ring map supplies the canonical finite-presentation instance
for its target algebra. -/
@[stacks 07D0 "finite-presentation instance for a local complete-intersection map"]
instance instFinitePresentation {f : A →+* B}
    [h : f.IsLocalCompleteIntersection] :
    @Algebra.FinitePresentation A B _ _ f.toAlgebra :=
  h.finitePresentation

/-- The empty polynomial algebra over `A` is canonically equivalent to `A`. -/
@[stacks 07D0 "empty polynomial algebra"]
noncomputable def empty_polynomial_algEquiv (A : Type u) [CommRing A] :
    MvPolynomial (Fin 0) A ≃ₐ[A] A :=
  (MvPolynomial.renameEquiv A (_root_.finZeroEquiv' : Fin 0 ≃ PEmpty.{u + 1})).trans
    (MvPolynomial.isEmptyAlgEquiv A PEmpty.{u + 1})

/-- The identity map has the empty finite polynomial presentation. -/
@[stacks 07D0 "empty presentation of the identity map"]
noncomputable def empty_identity_presentation (A : Type u) [CommRing A] :
    (RingHom.id A).Generators (Fin 0) :=
  Algebra.Generators.ofAlgHom
    (empty_polynomial_algEquiv A).toAlgHom
    (empty_polynomial_algEquiv A).surjective

/-- The kernel of the empty identity presentation is the zero ideal. -/
@[stacks 07D0 "kernel of the empty identity presentation"]
theorem empty_identity_presentation_ker_eq_bot (A : Type u) [CommRing A] :
    (empty_identity_presentation A).ker = ⊥ := sorry

/-- The zero ideal is Koszul-regular. -/
@[stacks 07D0 "Koszul regularity of the zero ideal"]
theorem bot_isKoszulRegularIdeal (R : Type u) [CommRing R] :
    ((⊥ : Ideal R)).IsKoszulRegularIdeal := sorry

/-- The identity ring homomorphism is a local complete intersection. -/
@[stacks 07D0 "identity local complete-intersection map"]
theorem id : (RingHom.id A).IsLocalCompleteIntersection := sorry

end IsLocalCompleteIntersection

end

end RingHom
