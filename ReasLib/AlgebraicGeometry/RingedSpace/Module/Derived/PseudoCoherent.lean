/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.PseudoCoherent
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Basic
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.OpensRingedSite
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Pseudo-coherent derived modules on ringed spaces

Pseudo-coherence on a ringed space is the specialization of the ringed-site predicates to its
canonical site of opens.  This file is the stable facade used by ringed-space developments;
open-cover characterizations live in `PseudoCoherent.Local`.
-/

open AlgebraicGeometry
open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace.{u}}

namespace CochainComplex

/-- A complex of `𝒪_X`-modules is `m`-pseudo-coherent when it satisfies the canonical
ringed-site approximation predicate. -/
@[stacks 08CB "complex m-version"]
abbrev IsMPseudoCoherent (E : _root_.CochainComplex (Modules X) ℤ) (m : ℤ) : Prop :=
  _root_.CochainComplex.IsMPseudoCoherent (X := opensRingedSite X) E m

/-- A complex of `𝒪_X`-modules is pseudo-coherent when it is `m`-pseudo-coherent for every
integer `m`. -/
@[stacks 08CB "complex version"]
abbrev IsPseudoCoherent (E : _root_.CochainComplex (Modules X) ℤ) : Prop :=
  _root_.CochainComplex.IsPseudoCoherent (X := opensRingedSite X) E

end CochainComplex

namespace ModuleDerived

/-- A derived `𝒪_X`-module is `m`-pseudo-coherent when it satisfies the canonical ringed-site
approximation predicate. -/
@[stacks 08CB "derived m-version"]
abbrev IsMPseudoCoherent (K : ModuleDerived X) (m : ℤ) : Prop :=
  RingedSite.Hom.ModuleDerived.IsMPseudoCoherent (X := opensRingedSite X) K m

/-- A derived `𝒪_X`-module is pseudo-coherent when it satisfies the canonical ringed-site
pseudo-coherence predicate. -/
@[stacks 08CB "derived version"]
abbrev IsPseudoCoherent (K : ModuleDerived X) : Prop :=
  RingedSite.Hom.ModuleDerived.IsPseudoCoherent (X := opensRingedSite X) K

/-- `m`-pseudo-coherence of a derived module is equivalent to admitting an
`m`-pseudo-coherent complex representative. -/
theorem isMPseudoCoherent_iff_exists_mPseudoCoherent_representative
    (K : ModuleDerived X) (m : ℤ) :
    IsMPseudoCoherent K m ↔
      ∃ E : _root_.CochainComplex (Modules X) ℤ,
        ∃ _ : K ≅ DerivedCategory.Q.obj E, CochainComplex.IsMPseudoCoherent E m := sorry

/-- Pseudo-coherence of a derived module is equivalent to admitting a pseudo-coherent complex
representative. -/
theorem isPseudoCoherent_iff_exists_pseudoCoherent_representative
    (K : ModuleDerived X) :
    IsPseudoCoherent K ↔
      ∃ E : _root_.CochainComplex (Modules X) ℤ,
        ∃ _ : K ≅ DerivedCategory.Q.obj E, CochainComplex.IsPseudoCoherent E := sorry

/-- A derived `𝒪_X`-module is pseudo-coherent exactly when it is `m`-pseudo-coherent for every
integer `m`. -/
theorem isPseudoCoherent_iff_forall_isMPseudoCoherent (K : ModuleDerived X) :
    IsPseudoCoherent K ↔ ∀ m : ℤ, IsMPseudoCoherent K m := sorry

/-- Every complex representing an `m`-pseudo-coherent derived module is `m`-pseudo-coherent. -/
@[stacks 08CC "representative bridge"]
theorem IsMPseudoCoherent.of_representation
    {K : ModuleDerived X} {E : _root_.CochainComplex (Modules X) ℤ} {m : ℤ}
    (hK : IsMPseudoCoherent K m) (e : DerivedCategory.Q.obj E ≅ K) :
    CochainComplex.IsMPseudoCoherent E m := sorry

/-- Every complex representing a pseudo-coherent derived module is pseudo-coherent. -/
theorem IsPseudoCoherent.of_representation
    {K : ModuleDerived X} {E : _root_.CochainComplex (Modules X) ℤ}
    (hK : IsPseudoCoherent K) (e : DerivedCategory.Q.obj E ≅ K) :
    CochainComplex.IsPseudoCoherent E := sorry

end ModuleDerived

namespace CochainComplex

/-- An `m`-pseudo-coherent complex defines an `m`-pseudo-coherent derived module. -/
theorem IsMPseudoCoherent.q_obj
    {E : _root_.CochainComplex (Modules X) ℤ} {m : ℤ}
    (hE : IsMPseudoCoherent E m) :
    ModuleDerived.IsMPseudoCoherent (DerivedCategory.Q.obj E) m := sorry

/-- A pseudo-coherent complex defines a pseudo-coherent derived module. -/
theorem IsPseudoCoherent.q_obj
    {E : _root_.CochainComplex (Modules X) ℤ}
    (hE : IsPseudoCoherent E) :
    ModuleDerived.IsPseudoCoherent (DerivedCategory.Q.obj E) := sorry

end CochainComplex

end AlgebraicGeometry.RingedSpace

namespace SheafOfModules

variable {X : AlgebraicGeometry.RingedSpace.{u}}

/-- A sheaf of `𝒪_X`-modules is `m`-pseudo-coherent when its degree-zero derived realization is
`m`-pseudo-coherent. -/
@[stacks 08CB "module m-version"]
abbrev IsMPseudoCoherent
    (F : AlgebraicGeometry.RingedSpace.Modules X) (m : ℤ) : Prop :=
  AlgebraicGeometry.RingedSpace.ModuleDerived.IsMPseudoCoherent
    ((DerivedCategory.singleFunctor (AlgebraicGeometry.RingedSpace.Modules X) (0 : ℤ)).obj F) m

/-- A sheaf of `𝒪_X`-modules is pseudo-coherent when its degree-zero derived realization is
pseudo-coherent. -/
@[stacks 08CB "module version"]
abbrev IsPseudoCoherent (F : AlgebraicGeometry.RingedSpace.Modules X) : Prop :=
  AlgebraicGeometry.RingedSpace.ModuleDerived.IsPseudoCoherent
    ((DerivedCategory.singleFunctor (AlgebraicGeometry.RingedSpace.Modules X) (0 : ℤ)).obj F)

end SheafOfModules
