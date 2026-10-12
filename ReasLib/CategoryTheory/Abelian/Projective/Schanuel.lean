/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Abelian.Projective.Basic
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import ReasLib.CategoryTheory.ShortComplex.KernelSequence
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Schanuel's lemma

The primary API is stated for two projective presentations in an abelian category.  The
short-complex formulation retains the full comparison diagram without exposing pullback choices
or epimorphic pullback projections to downstream users.

@stack 00O3
-/

noncomputable section

open CategoryTheory.Limits

universe u v

namespace CategoryTheory.ProjectivePresentation

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {X : C}

/-- The kernel short complex of a projective presentation. -/
@[stacks 00O3 "kernel sequence of a projective presentation"]
noncomputable abbrev kernelSequence (P : ProjectivePresentation X) : ShortComplex C :=
  ShortComplex.kernelSequence P.f

/-- The middle object of a projective presentation's kernel sequence is projective. -/
@[stacks 00O3 "projective middle term of a presentation"]
instance kernelSequence_projective (P : ProjectivePresentation X) :
    Projective P.kernelSequence.X₂ := by
  change Projective P.p
  infer_instance

/-- The final map of a projective presentation's kernel sequence is an epimorphism. -/
@[stacks 00O3 "epimorphic presentation map"]
instance kernelSequence_epi (P : ProjectivePresentation X) : Epi P.kernelSequence.g := by
  change Epi P.f
  infer_instance

/-- The kernel sequence of a projective presentation is short exact. -/
@[stacks 00O3 "exact kernel sequence of a projective presentation"]
theorem kernelSequence_shortExact (P : ProjectivePresentation X) :
    P.kernelSequence.ShortExact :=
  ShortComplex.kernelSequence_shortExact_of_epi P.f

end CategoryTheory.ProjectivePresentation

namespace CategoryTheory.ShortComplex.ShortExact

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {S₁ S₂ : ShortComplex C}

namespace Schanuel

/-- The stabilized inclusion associated to the first short exact sequence. -/
noncomputable abbrev leftInclusion :
    S₁.X₁ ⊞ S₂.X₂ ⟶ S₁.X₂ ⊞ S₂.X₂ :=
  biprod.map S₁.f (𝟙 _)

/-- The stabilized projection associated to the first short exact sequence. -/
noncomputable abbrev leftProjection :
    S₁.X₂ ⊞ S₂.X₂ ⟶ S₁.X₃ :=
  biprod.desc S₁.g 0

/-- The stabilized inclusion associated to the second short exact sequence. -/
noncomputable abbrev rightInclusion :
    S₁.X₂ ⊞ S₂.X₁ ⟶ S₁.X₂ ⊞ S₂.X₂ :=
  biprod.map (𝟙 _) S₂.f

/-- The stabilized projection associated to the second short exact sequence. -/
noncomputable abbrev rightProjection :
    S₁.X₂ ⊞ S₂.X₂ ⟶ S₂.X₃ :=
  biprod.desc 0 S₂.g

/-- The first stabilized row in Schanuel's diagram. -/
@[stacks 00O3 "first stabilized Schanuel row"]
noncomputable def leftSequence (S₁ S₂ : ShortComplex C) : ShortComplex C :=
  ShortComplex.mk
    (leftInclusion (S₁ := S₁) (S₂ := S₂))
    (leftProjection (S₁ := S₁) (S₂ := S₂))
    (by ext <;> simp)

/-- The second stabilized row in Schanuel's diagram. -/
@[stacks 00O3 "second stabilized Schanuel row"]
noncomputable def rightSequence (S₁ S₂ : ShortComplex C) : ShortComplex C :=
  ShortComplex.mk
    (rightInclusion (S₁ := S₁) (S₂ := S₂))
    (rightProjection (S₁ := S₁) (S₂ := S₂))
    (by ext <;> simp)

/-- Stabilizing a short exact sequence by an identity summand remains short exact. -/
@[stacks 00O3 "first stabilized Schanuel row is exact"]
theorem leftSequence_shortExact (h₁ : S₁.ShortExact) :
    (leftSequence S₁ S₂).ShortExact := sorry

/-- Stabilizing a short exact sequence by an identity summand remains short exact. -/
@[stacks 00O3 "second stabilized Schanuel row is exact"]
theorem rightSequence_shortExact (h₂ : S₂.ShortExact) :
    (rightSequence S₁ S₂).ShortExact := sorry

/-- The Schanuel comparison as an isomorphism of stabilized short complexes.  Its commuting
squares are the bundled laws of a `ShortComplex` isomorphism. -/
@[stacks 00O3 "Schanuel comparison diagram"]
noncomputable def diagram
    (h₁ : S₁.ShortExact) (h₂ : S₂.ShortExact) (e₃ : S₁.X₃ ≅ S₂.X₃)
    [Projective S₁.X₂] [Projective S₂.X₂] :
    leftSequence S₁ S₂ ≅ rightSequence S₁ S₂ := sorry

/-- The right component of the Schanuel comparison is the supplied quotient isomorphism. -/
@[stacks 00O3 "right component of the Schanuel diagram"]
theorem diagram_τ₃
    (h₁ : S₁.ShortExact) (h₂ : S₂.ShortExact) (e₃ : S₁.X₃ ≅ S₂.X₃)
    [Projective S₁.X₂] [Projective S₂.X₂] :
    (diagram h₁ h₂ e₃).hom.τ₃ = e₃.hom := sorry

end Schanuel

/-- Schanuel's stable isomorphism in the short-exact-complex formulation. -/
@[stacks 00O3 "short-exact-complex Schanuel isomorphism"]
noncomputable def schanuelIso
    (h₁ : S₁.ShortExact) (h₂ : S₂.ShortExact) (e₃ : S₁.X₃ ≅ S₂.X₃)
    [Projective S₁.X₂] [Projective S₂.X₂] :
    S₁.X₁ ⊞ S₂.X₂ ≅ S₁.X₂ ⊞ S₂.X₁ :=
  ShortComplex.π₁.mapIso (Schanuel.diagram h₁ h₂ e₃)

end CategoryTheory.ShortComplex.ShortExact

namespace CategoryTheory.ProjectivePresentation

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {X : C}

/-- The primary Schanuel datum for two projective presentations: an isomorphism of their
stabilized kernel sequences. -/
@[stacks 00O3 "projective-presentation Schanuel diagram"]
noncomputable def schanuelDiagram (P Q : ProjectivePresentation X) :
    ShortComplex.ShortExact.Schanuel.leftSequence P.kernelSequence Q.kernelSequence ≅
      ShortComplex.ShortExact.Schanuel.rightSequence P.kernelSequence Q.kernelSequence :=
  ShortComplex.ShortExact.Schanuel.diagram
    P.kernelSequence_shortExact Q.kernelSequence_shortExact (Iso.refl X)

/-- The comparison diagram is the identity on the presented object. -/
@[stacks 00O3 "right component of the projective-presentation Schanuel diagram"]
theorem schanuelDiagram_τ₃ (P Q : ProjectivePresentation X) :
    (schanuelDiagram P Q).hom.τ₃ = 𝟙 X := sorry

/-- Schanuel's stable isomorphism for two projective presentations of the same object.  This is
the low-parameter owner form: projectivity and epimorphicity are already bundled. -/
@[stacks 00O3 "projective-presentation Schanuel isomorphism"]
noncomputable def schanuelIso (P Q : ProjectivePresentation X) :
    kernel P.f ⊞ Q.p ≅ P.p ⊞ kernel Q.f :=
  ShortComplex.π₁.mapIso (schanuelDiagram P Q)

/-- Existence-only form of the projective-presentation Schanuel isomorphism. -/
theorem nonempty_schanuelIso (P Q : ProjectivePresentation X) :
    Nonempty (kernel P.f ⊞ Q.p ≅ P.p ⊞ kernel Q.f) :=
  ⟨schanuelIso P Q⟩

end CategoryTheory.ProjectivePresentation
