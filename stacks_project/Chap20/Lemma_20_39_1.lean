/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Pushforward
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.IdealPower.Principal.CohomologyDiagram
public import ReasLib.Algebra.Homology.DerivedCategory.ScalarExtension.Adjunction
import StacksCheckRecall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open AlgebraicGeometry
open CategoryTheory.DerivedCategory.PrincipalPower
open scoped RingedSpaceDerivedGlobalSections

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

section

variable {X : RingedSpace.{u}} {A : Type u} [CommRing A]

/- Domain-style sampling for Lemma 20.39.1:
- primary domain: principal derived-completion comparison diagrams specialized to derived global
  sections on a ringed space;
- sampled owner declarations:
  `globalSectionsRing X`,
  `moduleGlobalSectionsFunctor X`,
  `moduleDerivedGlobalSections X`,
  `CohomologyDiagram.existsComparison`;
  completion is then expressed with the chapter notation `K^∧[I, hI]`.
- best owner abstraction:
  `source-facing`: the ringed-space specialization with `K = RΓ(X, E)` for
    `E ∈ D(𝒪_X)`;
  `core/canonical`: `globalSectionsRing X`, `moduleGlobalSectionsFunctor X`,
  `moduleDerivedGlobalSections X`, `CohomologyDiagram.existsComparison`,
  and the chapter completion notation `K^∧[I, hI]`;
  `bridge/view`: the specialization of the Chapter 15 principal derived-completion comparison
    theorem along the Chapter 20 owner `moduleDerivedGlobalSections X`.
- primitive vs. derived:
  primitive data are the ringed space `X`, a scalar map `α : A →+* Γ(X,𝒪_X)`, an element `f : A`,
  and the derived object `E : DerivedCategory (RingedSpace.Modules X)`;
  the quotient/torsion towers, the completed object
  `(RΓ(X, E))^∧[(f), principalIdeal_fg f]`, and the comparison diagram are derived API.

Source/core/bridge triage:
- `source-facing`: Lemma 20.39.1, read as the comparison diagram for the cohomology of
  `RΓ(X, E)` after restriction of scalars along `α`, and its principal `f`-adic completion;
- `core/canonical`: `globalSectionsRing X`, `moduleDerivedGlobalSections X`,
  `CohomologyDiagram.existsComparison`, and `K^∧[I, hI]`;
- `bridge/view`: the global-sections specialization of the Chapter 15 comparison theorem.

This file should therefore remain a `bridge/view` recall item: it specializes the Chapter 15
comparison diagram to the canonical derived global-sections construction, transports scalars along
`α`, and exposes the principal `f`-adic completed object without introducing a second local theorem
shell.  The identification with the ringed-space derived inverse limit belongs to a future
ReasLib owner and is intentionally not hidden behind a false definitional equality here.
-/

variable (α : A →+* globalSectionsRing X) (f : A)
  (E : DerivedCategory (RingedSpace.Modules X)) (p : ℤ)

/- Lemma 20.39.1 (0H3C): this is the Chapter 15 principal derived-completion comparison diagram
specialized to `RΓ(X, E)` after restriction of scalars along `α : A →+* Γ(X, 𝒪_X)`. -/
@[stacks 0H3C]
#check
  (CohomologyDiagram.existsComparison f
    ((ModuleCat.derivedRestrictionOfScalars α).obj ((RΓ(X)).obj E)) p)

end

end AlgebraicGeometry.RingedSpace
