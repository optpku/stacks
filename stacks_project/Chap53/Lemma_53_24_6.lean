/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.OverField.RationalBridge.StableContraction

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry.Scheme
open Scheme.DerivedQCoh.ProperDualizingComplex
open scoped AlgebraicGeometry

universe u

/- Lemma 53.24.6 (1): the dualizing module of a terminal contraction endpoint is ample. -/
@[stacks 0E3Q] #check
  (AlgebraicGeometry.SchemeOverField.terminalContraction_curveDualizingModule_isAmple :
    ∀ {k : Type u} [Field k] (X : SchemeOverField k) [IsProper X.hom]
      (h_dimension : topologicalKrullDim X.left = 1)
      (h_global : Function.Bijective (Scheme.Hom.globalSectionsMap X.hom))
      (h_nodal : SchemeOverField.atWorstNodal X)
      (h_no_tail : ¬ Nonempty (SchemeOverField.RationalTail X))
      (h_genus : (2 : ℕ) ≤ SchemeOverField.genus X h_dimension h_global)
      {Y : SchemeOverField k}
      (chain : AlgebraicGeometry.RationalBridge.ContractionChain X Y)
      (h_no_bridge : ¬ Nonempty (AlgebraicGeometry.RationalBridge Y)),
      Scheme.Modules.isAmpleObject
        (@AlgebraicGeometry.Scheme.DerivedQCoh.ProperDualizingComplex.curveDualizingModule
          k _ Y.left Y.hom chain.target_proper))

/- Lemma 53.24.6 (2): terminal contraction endpoints are independent of the choices, up to an
isomorphism commuting with the two induced contraction morphisms. -/
@[stacks 0E3Q] #check
  (AlgebraicGeometry.SchemeOverField.stableContraction_independent :
    ∀ {k : Type u} [Field k] (X : SchemeOverField k) [IsProper X.hom]
      (h_dimension : topologicalKrullDim X.left = 1)
      (h_global : Function.Bijective (Scheme.Hom.globalSectionsMap X.hom))
      (h_nodal : SchemeOverField.atWorstNodal X)
      (h_no_tail : ¬ Nonempty (SchemeOverField.RationalTail X))
      (h_genus : (2 : ℕ) ≤ SchemeOverField.genus X h_dimension h_global)
      {Y₁ Y₂ : SchemeOverField k}
      (chain₁ : AlgebraicGeometry.RationalBridge.ContractionChain X Y₁)
      (h₁ : ¬ Nonempty (AlgebraicGeometry.RationalBridge Y₁))
      (chain₂ : AlgebraicGeometry.RationalBridge.ContractionChain X Y₂)
      (h₂ : ¬ Nonempty (AlgebraicGeometry.RationalBridge Y₂)),
      ∃! e : Y₁ ≅ Y₂, chain₁.map ≫ e.hom = chain₂.map)

/- Lemma 53.24.6 (3): after a field extension, the base-changed contraction morphism is
represented by a concrete rational-bridge contraction chain. -/
@[stacks 0E3Q] #check
  (AlgebraicGeometry.SchemeOverField.stableContraction_existsBaseChange :
    ∀ {k K : Type u} [Field k] [Field K] [Algebra k K]
      (X : SchemeOverField k) [IsProper X.hom]
      (h_dimension : topologicalKrullDim X.left = 1)
      (h_global : Function.Bijective (Scheme.Hom.globalSectionsMap X.hom))
      (h_nodal : SchemeOverField.atWorstNodal X)
      (h_no_tail : ¬ Nonempty (SchemeOverField.RationalTail X))
      (h_genus : (2 : ℕ) ≤ SchemeOverField.genus X h_dimension h_global)
      {Y : SchemeOverField k}
      (chain : AlgebraicGeometry.RationalBridge.ContractionChain X Y)
      (h_no_bridge : ¬ Nonempty (AlgebraicGeometry.RationalBridge Y)),
      ∃ chainK : AlgebraicGeometry.RationalBridge.ContractionChain
          (AlgebraicGeometry.FieldExtension.Over.baseChange k K X)
          (AlgebraicGeometry.FieldExtension.Over.baseChange k K Y),
        chainK.map = (AlgebraicGeometry.FieldExtension.Over.functor k K).map chain.map)

/- Lemma 53.24.6 (4): rational bridges do not reappear on the endpoint after extending the
ground field. -/
@[stacks 0E3Q] #check
  (AlgebraicGeometry.SchemeOverField.stableContraction_baseChangeNoBridge :
    ∀ {k K : Type u} [Field k] [Field K] [Algebra k K]
      (X : SchemeOverField k) [IsProper X.hom]
      (h_dimension : topologicalKrullDim X.left = 1)
      (h_global : Function.Bijective (Scheme.Hom.globalSectionsMap X.hom))
      (h_nodal : SchemeOverField.atWorstNodal X)
      (h_no_tail : ¬ Nonempty (SchemeOverField.RationalTail X))
      (h_genus : (2 : ℕ) ≤ SchemeOverField.genus X h_dimension h_global)
      {Y : SchemeOverField k}
      (chain : AlgebraicGeometry.RationalBridge.ContractionChain X Y)
      (h_no_bridge : ¬ Nonempty (AlgebraicGeometry.RationalBridge Y)),
      ¬ Nonempty
        (AlgebraicGeometry.RationalBridge
          (AlgebraicGeometry.FieldExtension.Over.baseChange k K Y)))

/- Lemma 53.24.6 (5): every terminal base-changed contraction chain has a unique endpoint
isomorphism compatible with the base-changed original contraction morphism. -/
@[stacks 0E3Q] #check
  (AlgebraicGeometry.SchemeOverField.stableContraction_commutesWithBaseChange :
    ∀ {k K : Type u} [Field k] [Field K] [Algebra k K]
      (X : SchemeOverField k) [IsProper X.hom]
      (h_dimension : topologicalKrullDim X.left = 1)
      (h_global : Function.Bijective (Scheme.Hom.globalSectionsMap X.hom))
      (h_nodal : SchemeOverField.atWorstNodal X)
      (h_no_tail : ¬ Nonempty (SchemeOverField.RationalTail X))
      (h_genus : (2 : ℕ) ≤ SchemeOverField.genus X h_dimension h_global)
      {Y : SchemeOverField k}
      (chain : AlgebraicGeometry.RationalBridge.ContractionChain X Y)
      (h_no_bridge : ¬ Nonempty (AlgebraicGeometry.RationalBridge Y))
      {YK : SchemeOverField K}
      (chainK : AlgebraicGeometry.RationalBridge.ContractionChain
        (AlgebraicGeometry.FieldExtension.Over.baseChange k K X) YK)
      (h_no_bridgeK : ¬ Nonempty (AlgebraicGeometry.RationalBridge YK)),
      ∃! e : AlgebraicGeometry.FieldExtension.Over.baseChange k K Y ≅ YK,
        (AlgebraicGeometry.FieldExtension.Over.functor k K).map chain.map ≫ e.hom = chainK.map)
