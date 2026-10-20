/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Combinatorics.Quiver.Path
public import ReasLib.AlgebraicGeometry.Scheme.OverField.RationalTail

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open AlgebraicGeometry.Scheme

noncomputable section

universe u

namespace AlgebraicGeometry
namespace SchemeOverField
namespace RationalTail

/-- A single rational-tail contraction, including its selected tail, contraction morphism,
and identification of the target with the complementary closure. -/
structure Contraction {k : Type u} [Field k] (X Y : SchemeOverField k) where
  /-- The rational tail selected for contraction. -/
  tail : RationalTail X
  /-- The contraction morphism over the ground field. -/
  hom : X ⟶ Y
  /-- The target is identified with the scheme-theoretic closure of the complement. -/
  targetIso : complementOver X tail.component ≅ Y
  /-- On the complementary closure, the contraction agrees with the target identification. -/
  restrictsToComplement :
    (complementIdeal X tail.component).subschemeι ≫ hom.left = targetIso.hom.left
  /-- On the selected component, the contraction is the canonical collapse. -/
  restrictsToComponent :
    (componentIdeal X tail.component).subschemeι ≫ hom.left =
      tail.collapse ≫ targetIso.hom.left

namespace Contraction

/-- Construct a rational-tail contraction from its explicit geometric data and restriction
laws. -/
def ofData {k : Type u} [Field k] (X Y : SchemeOverField k)
    (tail : RationalTail X) (hom : X ⟶ Y)
    (targetIso : complementOver X tail.component ≅ Y)
    (restrictsToComplement :
      (complementIdeal X tail.component).subschemeι ≫ hom.left = targetIso.hom.left)
    (restrictsToComponent :
      (componentIdeal X tail.component).subschemeι ≫ hom.left =
        tail.collapse ≫ targetIso.hom.left) :
    Contraction X Y :=
  { tail := tail
    hom := hom
    targetIso := targetIso
    restrictsToComplement := restrictsToComplement
    restrictsToComponent := restrictsToComponent }

/-- A rational-tail contraction satisfies its complementary and component restriction laws. -/
theorem spec {k : Type u} [Field k] {X Y : SchemeOverField k}
    (step : Contraction X Y) :
    (complementIdeal X step.tail.component).subschemeι ≫ step.hom.left =
        step.targetIso.hom.left ∧
      (componentIdeal X step.tail.component).subschemeι ≫ step.hom.left =
        step.tail.collapse ≫ step.targetIso.hom.left := sorry

end Contraction

end RationalTail
end SchemeOverField
end AlgebraicGeometry

/-- A finite sequence of rational-tail contractions from a scheme to an explicitly chosen
endpoint, represented as a path in the reversed quiver of contraction steps. -/
def AlgebraicGeometry.SchemeOverField.RationalTail.ContractionChain {k : Type u} [Field k]
    (X Y : SchemeOverField k) :=
  @Quiver.Path (SchemeOverField k) ⟨fun target source => Contraction source target⟩ Y X

namespace AlgebraicGeometry
namespace SchemeOverField
namespace RationalTail

namespace ContractionChain

/-- The empty contraction sequence from a scheme to itself. -/
def refl {k : Type u} [Field k] (X : SchemeOverField k) : ContractionChain X X :=
  @Quiver.Path.nil (SchemeOverField k) ⟨fun target source => Contraction source target⟩ X

/-- Prepend one rational-tail contraction to a finite contraction sequence. -/
def cons {k : Type u} [Field k] {X Y Z : SchemeOverField k}
    (step : Contraction X Y) (tail : ContractionChain Y Z) : ContractionChain X Z :=
  @Quiver.Path.cons (SchemeOverField k) ⟨fun target source => Contraction source target⟩
    Z Y X tail step

/-- The morphism represented by a contraction chain is the composite of its step maps. -/
def map {k : Type u} [Field k] {X Y : SchemeOverField k}
    (chain : ContractionChain X Y) : X ⟶ Y :=
  @Quiver.Path.rec (SchemeOverField k) ⟨fun target source => Contraction source target⟩
    Y (fun source _ => source ⟶ Y) (𝟙 Y)
    (fun {_ _} _ step tailMap => step.hom ≫ tailMap) X chain

/-- Regard one rational-tail contraction as a one-step contraction chain. -/
def single {k : Type u} [Field k] {X Y : SchemeOverField k}
    (step : Contraction X Y) : ContractionChain X Y :=
  cons step (refl Y)

/-- The map of the empty contraction chain is the identity. -/
theorem map_refl {k : Type u} [Field k] (X : SchemeOverField k) :
    (refl X : ContractionChain X X).map = 𝟙 X := sorry

/-- The map of a cons chain is the first contraction followed by the remaining composite. -/
theorem map_cons {k : Type u} [Field k] {X Y Z : SchemeOverField k}
    (step : Contraction X Y) (rest : ContractionChain Y Z) :
    (cons step rest).map = step.hom ≫ rest.map := sorry

/-- A rational-tail contraction chain preserves properness over the ground field. -/
theorem targetProper {k : Type u} [Field k] {X Y : SchemeOverField k}
    [IsProper X.hom] (chain : ContractionChain X Y) : IsProper Y.hom := sorry

/-- A rational-tail contraction chain preserves one-dimensionality. -/
theorem targetDimension {k : Type u} [Field k] {X Y : SchemeOverField k}
    [IsProper X.hom] (chain : ContractionChain X Y)
    (h_dimension : topologicalKrullDim X.left = 1)
    (h_global : Function.Bijective (Scheme.Hom.globalSectionsMap X.hom))
    (h_nodal : atWorstNodal X) :
    topologicalKrullDim Y.left = 1 := sorry

/-- A rational-tail contraction chain preserves constant global functions. -/
theorem targetGlobalSections {k : Type u} [Field k] {X Y : SchemeOverField k}
    [IsProper X.hom] (chain : ContractionChain X Y)
    (h_dimension : topologicalKrullDim X.left = 1)
    (h_global : Function.Bijective (Scheme.Hom.globalSectionsMap X.hom))
    (h_nodal : atWorstNodal X) :
    Function.Bijective (Scheme.Hom.globalSectionsMap Y.hom) := sorry

/-- A rational-tail contraction chain preserves at-worst-nodal singularities. -/
theorem targetAtWorstNodal {k : Type u} [Field k] {X Y : SchemeOverField k}
    [IsProper X.hom] (chain : ContractionChain X Y)
    (h_dimension : topologicalKrullDim X.left = 1)
    (h_global : Function.Bijective (Scheme.Hom.globalSectionsMap X.hom))
    (h_nodal : atWorstNodal X) :
    atWorstNodal Y := sorry

/-- A rational-tail contraction chain preserves the genus. -/
theorem targetGenusEq {k : Type u} [Field k] {X Y : SchemeOverField k}
    [IsProper X.hom] (chain : ContractionChain X Y)
    (h_dimension : topologicalKrullDim X.left = 1)
    (h_global : Function.Bijective (Scheme.Hom.globalSectionsMap X.hom))
    (h_nodal : atWorstNodal X) :
    Scheme.Hom.cohomologyFinrank Y.hom
        (SheafOfModules.unit Y.left.ringCatSheaf : Y.left.Modules) 1 =
      Scheme.Hom.cohomologyFinrank X.hom
        (SheafOfModules.unit X.left.ringCatSheaf : X.left.Modules) 1 := sorry

end ContractionChain

end RationalTail
end SchemeOverField
end AlgebraicGeometry
