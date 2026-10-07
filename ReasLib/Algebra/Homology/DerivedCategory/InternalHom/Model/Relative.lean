module

public import ReasLib.Algebra.Homology.CochainComplex.HomComplex.Relative
public import ReasLib.Algebra.Homology.DerivedCategory.InternalHom.Model.RHom
public import ReasLib.Algebra.Homology.DerivedCategory.PseudoCoherent.Relative.FlatModel
public import ReasLib.Algebra.Homology.DerivedCategory.TorAmplitude.Relative.Model
import ReasLib.Algebra.Homology.DerivedCategory.PseudoCoherent.Model
public import Mathlib.RingTheory.FinitePresentation
import Mathlib.Tactic.CrossRefAttribute

/-!
# Relative models for derived internal Hom

This leaf composes the independent representative producers with the fixed Hom-complex owners.
Its primary statements target canonical `InternalHom.RHom.obj`; an optional closed-owner bridge is
available in the sibling `InternalHom.Model.RHom.Closed` leaf and is deliberately not a prerequisite
for the source-facing model producer.
The finite-Tor theorem is the basic reusable result; `IsPerfectOver.exists_internalHom_model` is
its relative-perfect refinement.  Producers return the representative comparison isomorphisms as
explicit witnesses, while the fixed-model comparison leaves remain proposition-valued.  Neither
generalized producer requires the finite-presentation hypothesis on the algebra map; the
finite-presentation specialization restores that source-facing ambient assumption when it is part
of the statement.  This source-facing producer currently follows the standard same-universe
`DerivedCategory (ModuleCat A)` presentation used by its lower representative producers; the
short `InternalHom.RHom` facade has the same boundary.  The generic enriched owner and
`InternalHom.RHom.At` remain carrier-polymorphic; a higher-universe relative producer should be
added only together with corresponding lower model owners.

@stack 0E1U
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory
open CochainComplex.HomComplex

namespace CategoryTheory.DerivedCategory

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
variable [Module.Flat R A]
variable {K L : DerivedCategory (ModuleCat A)}

namespace InternalHom.RHom

/-- A concrete relative model computing canonical `RHom(K, L)` from a bounded-above finite-free
source and a bounded relatively flat target.  All representative and comparison data are named
fields, so downstream arguments do not depend on the nesting order of an existential package. -/
@[stacks 0E1U "relative finite-Tor RHom model"]
structure FiniteTorModel (R : Type u) [CommRing R]
    {A : Type u} [CommRing A] [Algebra R A]
    (K L : DerivedCategory (ModuleCat A)) where
  /-- The bounded-above finite-free source representative. -/
  source : CochainComplex (ModuleCat A) ℤ
  /-- The bounded relatively flat target representative. -/
  target : CochainComplex (ModuleCat A) ℤ
  /-- Identification of the source representative with `K`. -/
  sourceIso : DerivedCategory.Q.obj source ≅ K
  /-- Identification of the target representative with `L`. -/
  targetIso : DerivedCategory.Q.obj target ≅ L
  /-- Identification of the strict Hom complex with canonical `RHom(K, L)`. -/
  rhomIso : DerivedCategory.Q.obj (moduleComplex A source target) ≅
    InternalHom.RHom.obj (A := A) K L
  /-- The source is bounded above. -/
  sourceMinus : CochainComplex.minus (ModuleCat A) source
  /-- Every source term is finite free. -/
  sourceFiniteFree : source.IsTermwiseFiniteFree
  /-- The target is bounded on both sides. -/
  targetBounded : CochainComplex.bounded (ModuleCat A) target
  /-- Every target term is flat over the base ring. -/
  targetFlat : target.IsTermwiseFlatOver R
  /-- The strict Hom complex is bounded below. -/
  homPlus : CochainComplex.plus (ModuleCat A) (moduleComplex A source target)
  /-- Every term of the strict Hom complex is flat over the base ring. -/
  homFlat : (moduleComplex A source target).IsTermwiseFlatOver R

/-- The relative-perfect refinement of `FiniteTorModel`, recording finite presentation of the
target and of the resulting strict Hom complex. -/
@[stacks 0E1U "relative perfect RHom model"]
structure PerfectModel (R : Type u) [CommRing R]
    {A : Type u} [CommRing A] [Algebra R A]
    (K L : DerivedCategory (ModuleCat A)) extends FiniteTorModel R K L where
  /-- Every target term is finitely presented over `A`. -/
  targetFinitePresentation : target.IsTermwiseFinitePresentation
  /-- Every term of the strict Hom complex is finitely presented over `A`. -/
  homFinitePresentation :
    (moduleComplex A source target).IsTermwiseFinitePresentation

end InternalHom.RHom

namespace InternalHom.RHom.FiniteTorModel

/-- Lemma 15.85.6 (Stacks `0E1U`): a pseudo-coherent source and a target of finite Tor dimension
over `R` admit a concrete structured model computing canonical `RHom`. -/
@[stacks 0E1U "relative finite-Tor RHom model"]
theorem nonempty
    (hK : K.IsPseudoCoherent)
    (hL : L.HasFiniteTorDimensionOver R) :
    Nonempty (InternalHom.RHom.FiniteTorModel R K L) := by
  rcases hK.exists_finiteFree_model with ⟨P, eP, hPminus, hPfree⟩
  rcases hL.exists_flat_model with ⟨F, eF, hFbounded, hFflat⟩
  obtain ⟨hFplus, -⟩ :=
    (CochainComplex.bounded_iff (ModuleCat A) F).mp hFbounded
  have hPfp := HomologicalComplex.IsTermwiseFiniteProjective.of_finiteFree hPfree
  rcases CochainComplex.ProjectiveMinus.representsRHom_of_models
      P F eP eF hPminus hPfp with ⟨eRHom⟩
  exact ⟨{
    source := P
    target := F
    sourceIso := eP
    targetIso := eF
    rhomIso := eRHom
    sourceMinus := hPminus
    sourceFiniteFree := hPfree
    targetBounded := hFbounded
    targetFlat := hFflat
    homPlus := CochainComplex.HomComplex.plus hPminus hFplus
    homFlat := CochainComplex.HomComplex.isTermwiseFlatOver
      P F hPminus hPfp hFplus hFflat }⟩

end InternalHom.RHom.FiniteTorModel

namespace IsPseudoCoherent

/-- Source-facing compatibility name for the structured canonical `RHom` model producer. -/
abbrev exists_internalHom_model
    (hK : K.IsPseudoCoherent)
    (hL : L.HasFiniteTorDimensionOver R) :
    Nonempty (InternalHom.RHom.FiniteTorModel R K L) :=
  InternalHom.RHom.FiniteTorModel.nonempty hK hL

end IsPseudoCoherent

namespace InternalHom.RHom.PerfectModel

/-- Lemma 15.85.6 (Stacks `0E1U`): under relative perfectness, a structured perfect model computes
canonical `RHom` and records the finite-presentation refinements of its representatives. -/
@[stacks 0E1U "relative perfect RHom model"]
theorem nonempty
    (hK : K.IsPseudoCoherent)
    (hL : IsPerfectOver R L) :
    Nonempty (InternalHom.RHom.PerfectModel R K L) := by
  rcases hK.exists_finiteFree_model with ⟨P, eP, hPminus, hPfree⟩
  rcases hL.exists_flat_finitePresentation_model with
    ⟨F, eF, hFbounded, hFflat, hFfinite⟩
  obtain ⟨hFplus, -⟩ :=
    (CochainComplex.bounded_iff (ModuleCat A) F).mp hFbounded
  have hPfp := HomologicalComplex.IsTermwiseFiniteProjective.of_finiteFree hPfree
  rcases CochainComplex.ProjectiveMinus.representsRHom_of_models
      P F eP eF hPminus hPfp with ⟨eRHom⟩
  exact ⟨{
    source := P
    target := F
    sourceIso := eP
    targetIso := eF
    rhomIso := eRHom
    sourceMinus := hPminus
    sourceFiniteFree := hPfree
    targetBounded := hFbounded
    targetFlat := hFflat
    homPlus := CochainComplex.HomComplex.plus hPminus hFplus
    homFlat := CochainComplex.HomComplex.isTermwiseFlatOver
      P F hPminus hPfp hFplus hFflat
    targetFinitePresentation := hFfinite
    homFinitePresentation := CochainComplex.HomComplex.isTermwiseFinitePresentation
      P F hPminus hPfp hFplus hFfinite }⟩

end InternalHom.RHom.PerfectModel

namespace IsPerfectOver

/-- Source-facing compatibility name for the structured relative-perfect `RHom` producer. -/
abbrev exists_internalHom_model
    (hK : K.IsPseudoCoherent)
    (hL : IsPerfectOver R L) :
    Nonempty (InternalHom.RHom.PerfectModel R K L) :=
  InternalHom.RHom.PerfectModel.nonempty hK hL

namespace FinitePresentation

/-- With the source hypothesis that `R → A` is of finite presentation, the relative-perfect model
producer returns the finite-presentation refinement in the source's ambient layer (Lemma 15.85.6,
Stacks `0E1U`).  `IsPerfectOver.exists_internalHom_model` remains available without this source
assumption. -/
@[stacks 0E1U "finite-presentation map specialization of the relative internal-Hom model"]
abbrev exists_internalHom_model
    [Algebra.FinitePresentation R A] (hK : K.IsPseudoCoherent)
    (hL : IsPerfectOver R L) :
    Nonempty (InternalHom.RHom.PerfectModel R K L) :=
  InternalHom.RHom.PerfectModel.nonempty hK hL

end FinitePresentation

end IsPerfectOver

end CategoryTheory.DerivedCategory
