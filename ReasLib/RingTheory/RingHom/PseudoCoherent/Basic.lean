/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.PseudoCoherent.Relative.Basic

/-!
# Pseudo-coherent ring maps

The relative pseudo-coherence of complexes is owned by the derived-category
layer.  This leaf packages the corresponding intrinsic property of an explicit
commutative ring homomorphism.

@stack 067H
-/

@[expose] public section

noncomputable section

open CategoryTheory

universe u v

namespace RingHom

/-- A commutative ring map is pseudo-coherent when it is of finite type and its target regular
module is pseudo-coherent relative to the source. -/
@[stacks 067H "Definition 15.83.1 (1), pseudo-coherent ring map"]
class IsPseudoCoherentRingMap
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] (f : A →+* B) : Prop where
  /-- The ring map is of finite type. -/
  finiteType : f.FiniteType
  /-- The target regular module is pseudo-coherent relative to the source. -/
  isPseudoCoherentRelativeTo :
    let _ : Algebra A B := f.toAlgebra
    let _ : Algebra.FiniteType A B := RingHom.finiteType_algebraMap.mp finiteType
    (ModuleCat.of B B).IsPseudoCoherentRelativeTo A

/-- A pseudo-coherent ring map is exactly a finite type ring map whose target regular module is
pseudo-coherent relative to the source. -/
theorem isPseudoCoherentRingMap_iff
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] (f : A →+* B) :
    f.IsPseudoCoherentRingMap ↔
      ∃ h_finiteType : f.FiniteType,
        let _ : Algebra A B := f.toAlgebra
        let _ : Algebra.FiniteType A B := RingHom.finiteType_algebraMap.mp h_finiteType
        (ModuleCat.of B B).IsPseudoCoherentRelativeTo A := sorry
/- Proof strategy: unfold `IsPseudoCoherentRingMap`; the forward implication exposes its
`finiteType` and `isPseudoCoherentRelativeTo` fields, while the reverse implication applies the
class constructor after installing the algebra and finite-type structures induced by `f`. -/

/-- The identity homomorphism of a commutative ring is pseudo-coherent. -/
instance instIsPseudoCoherentRingMapId (A : Type u) [CommRing A] :
    (RingHom.id A).IsPseudoCoherentRingMap := sorry
/- Proof strategy: use the zero-variable identity polynomial presentation for finite type, then
identify the target regular module with the degree-zero self-relative pseudo-coherent object from
the relative derived-category API. -/

namespace IsPseudoCoherentRingMap

/-- The pseudo-coherent ring-map hypothesis supplies relative pseudo-coherence of the target
regular module for the algebra structure induced by the ring map itself. -/
theorem targetRegularModule_isPseudoCoherentRelativeTo
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] {f : A →+* B}
    (h : f.IsPseudoCoherentRingMap) :
    let _ : Algebra A B := f.toAlgebra
    let _ : Algebra.FiniteType A B := RingHom.finiteType_algebraMap.mp h.finiteType
    (ModuleCat.of B B).IsPseudoCoherentRelativeTo A := sorry
/- Proof strategy: install the algebra and finite-type structures determined by `f`, then project
`h.isPseudoCoherentRelativeTo`; the remaining obligation is definitional equality of the pinned
instances. -/

end IsPseudoCoherentRingMap

end RingHom

namespace Algebra

/-- A pseudo-coherent structure map supplies the finite type algebra instance needed by the
relative pseudo-coherence API. -/
instance (priority := 100) finiteType_of_isPseudoCoherentRingMap
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    [(algebraMap A B).IsPseudoCoherentRingMap] : Algebra.FiniteType A B := sorry
/- Proof strategy: project `RingHom.IsPseudoCoherentRingMap.finiteType` from the algebra map and
transport it through `RingHom.finiteType_algebraMap`. -/

/-- A pseudo-coherent algebra map makes its target regular module pseudo-coherent relative to
the source.  This algebra-map specialization avoids exposing the auxiliary `f.toAlgebra`
structure used by the intrinsic ring-hom owner. -/
theorem targetRegularModule_isPseudoCoherentRelativeTo
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    [(algebraMap A B).IsPseudoCoherentRingMap] :
    (ModuleCat.of B B).IsPseudoCoherentRelativeTo A := sorry
/- Proof strategy: apply
`RingHom.IsPseudoCoherentRingMap.targetRegularModule_isPseudoCoherentRelativeTo` to the algebra
map and discharge the induced-algebra comparison by extensionality. -/

end Algebra
