/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalSpectrum.FiniteType
import StacksCheckRecall

/-!
# Finite type morphisms of formal spectra

A continuous map of weakly admissible topological rings over a scheme `S`
induces a finite type morphism of formal spectra if and only if it is taut
and topologically of finite type.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.AffineFormalAlgebraicSpace

universe u

/- Lemma 87.29.2: Let `S` be a scheme. Let `φ : A →+* B` be a continuous map
of weakly admissible topological rings over `S`. Then
`spfMap φ : spf B hB ⟶ spf A hA` is of finite type if and only if `φ` is taut
and `B` is topologically of finite type over `A`. -/
@[stacks 0ANT] #check
  (AlgebraicGeometry.AffineFormalAlgebraicSpace.spfMap_finiteType_iff :
    ∀ {A B : Type u} [CommRing A] [TopologicalSpace A]
      [TopologicalRing.IsWeaklyAdmissibleRing A] [CommRing B] [TopologicalSpace B]
      [TopologicalRing.IsWeaklyAdmissibleRing B] {S : Scheme.{u}}
      (hA : Spec (.of A) ⟶ S) (hB : Spec (.of B) ⟶ S) (φ : A →+* B)
      (hφ : Continuous φ) (h_over : Spec.map (CommRingCat.ofHom φ) ≫ hA = hB)
      [HasWeakSheafify (Scheme.fppfTopology.over S) (Type u)],
    FormalAlgebraicSpace.FiniteType
        ((sheafToPresheaf (Scheme.fppfTopology.over S) (Type u)).map
          (spfMap φ hφ h_over)) ↔
      φ.IsTaut ∧ φ.TopologicallyOfFiniteType)
