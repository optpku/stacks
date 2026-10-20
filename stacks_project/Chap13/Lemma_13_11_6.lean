module

import ReasLib.CategoryTheory.DerivedCategory.BoundedLocalization
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 13.11.6

The bounded quasi-isomorphism systems, acyclic kernels, localization functors, and representative
bounds are all owned by the namespaced ReasLib API.  No chapter-level compatibility aliases are
introduced here.
-/

noncomputable section

open CategoryTheory.MorphismProperty CategoryTheory.ObjectProperty
open scoped CategoryTheory

universe w v u

namespace CategoryTheory

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜] [HasDerivedCategory.{w} 𝒜]

@[stacks 05RW "bounded-below derived representatives"]
#check @DerivedCategory.Plus.Qh.object_mem
@[stacks 05RW "bounded-below derived representatives"]
#check @DerivedCategory.Plus.Representative.homology_eventually_zero
@[stacks 05RW "bounded-below derived representatives"]
#check @DerivedCategory.Plus.Qh.essSurj
@[stacks 05RW "bounded-above derived representatives"]
#check @DerivedCategory.Minus.Qh.object_mem
@[stacks 05RW "bounded-above derived representatives"]
#check @DerivedCategory.Minus.Representative.homology_eventually_zero
@[stacks 05RW "bounded-above derived representatives"]
#check @DerivedCategory.Minus.Qh.essSurj
@[stacks 05RW "bounded derived representatives"]
#check @DerivedCategory.Bounded.Qh.object_mem
@[stacks 05RW "bounded derived representatives"]
#check @DerivedCategory.Bounded.Representative.homology_eventually_zero
@[stacks 05RW "bounded derived representatives"]
#check @DerivedCategory.Bounded.Qh.essSurj

/- Lemma 13.11.6 (1): bounded-below acyclic morphisms are bounded-below quasi-isomorphisms. -/
@[stacks 05RW "bounded-below acyclic Verdier system"]
#check HomotopyCategory.Plus.acyclic_trW_eq_quasiIso

/- Lemma 13.11.6 (2): the kernel of the bounded-below localization is the acyclic property. -/
@[stacks 05RW "kernel of bounded-below derived localization"]
#check @DerivedCategory.Plus.Qh.kernel_eq_acyclic

/- Lemma 13.11.6 (3): `D⁺(𝒜)` is the localization of `K⁺(𝒜)` at quasi-isomorphisms. -/
@[stacks 05RW "bounded-below derived localization"]
#check (inferInstance :
  (DerivedCategory.Plus.Qh : HomotopyCategory.Plus 𝒜 ⥤ DerivedCategory.Plus 𝒜).IsLocalization
    (HomotopyCategory.Plus.quasiIso 𝒜))

/- Lemma 13.11.6 (4): bounded-above acyclic morphisms are bounded-above quasi-isomorphisms. -/
@[stacks 05RW "bounded-above acyclic Verdier system"]
#check HomotopyCategory.Minus.acyclic_trW_eq_quasiIso

/- Lemma 13.11.6 (5): the kernel of the bounded-above localization is the acyclic property. -/
@[stacks 05RW "kernel of bounded-above derived localization"]
#check @DerivedCategory.Minus.Qh.kernel_eq_acyclic

/- Lemma 13.11.6 (6): `D⁻(𝒜)` is the localization of `K⁻(𝒜)` at quasi-isomorphisms. -/
@[stacks 05RW "bounded-above derived localization"]
#check (inferInstance :
  (DerivedCategory.Minus.Qh 𝒜).IsLocalization
    (HomotopyCategory.Minus.quasiIso 𝒜))

/- Lemma 13.11.6 (7): bounded acyclic morphisms are bounded quasi-isomorphisms. -/
@[stacks 05RW "bounded acyclic Verdier system"]
#check HomotopyCategory.Bounded.acyclic_trW_eq_quasiIso

/- Lemma 13.11.6 (8): the kernel of the bounded localization is the acyclic property. -/
@[stacks 05RW "kernel of bounded derived localization"]
#check @DerivedCategory.Bounded.Qh.kernel_eq_acyclic

/- Lemma 13.11.6 (9): `Dᵇ(𝒜)` is the localization of `Kᵇ(𝒜)` at quasi-isomorphisms. -/
@[stacks 05RW "bounded derived localization"]
#check (inferInstance :
  (DerivedCategory.Bounded.Qh 𝒜).IsLocalization
    (HomotopyCategory.Bounded.quasiIso 𝒜))

end CategoryTheory
