/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Extension.Obstruction
public import stacks_project.Chap91.«91_4_0_1_Extension»
public import ReasLib.CategoryTheory.Abelian.Extension.Ext

/-! Fixed-endpoint presentations of the homology sequences for maps of module extensions. -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.RingedSpace
open AlgebraicGeometry.RingedSpace.Hom
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.Hom.ModuleExtension

variable {X X' : RingedSpace.{u}} {i : X ⟶ X'}

/-- Pushout of a mixed-scalar extension along a map of kernel modules. -/
def pushoutExtension (E : ModuleExtension i) {K : X.Modules}
    (ψ : E.kernel ⟶ K) :
    CategoryTheory.Extension ((i _*).obj K) ((i _*).obj E.cokernel) :=
  CategoryTheory.Extension.pushout ((i _*).map ψ) E.toExtension

/-- Pullback of a mixed-scalar extension along a map of quotient modules. -/
def pullbackExtension (G : ModuleExtension i) {F : X.Modules}
    (φ : F ⟶ G.cokernel) :
    CategoryTheory.Extension ((i _*).obj G.kernel) ((i _*).obj F) :=
  CategoryTheory.Extension.pullback ((i _*).map φ) G.toExtension

/-- The fixed-endpoint extension represented by the difference complex's middle homology. -/
def differenceExtension (E G : ModuleExtension i)
    (φ : E.cokernel ⟶ G.cokernel) (ψ : E.kernel ⟶ G.kernel) :
    CategoryTheory.Extension ((i _*).obj G.kernel) ((i _*).obj E.cokernel) where
  E := (differenceSequence E G φ ψ).X₂
  f := (differenceSequence E G φ ψ).f
  g := (differenceSequence E G φ ψ).g
  zero := (differenceSequence E G φ ψ).zero
  shortExact := differenceSequence_shortExact E G φ ψ

/-- The difference extension has middle object canonically identified with difference homology. -/
def differenceExtension_homology (E G : ModuleExtension i)
    (φ : E.cokernel ⟶ G.cokernel) (ψ : E.kernel ⟶ G.kernel) :
    (differenceExtension E G φ ψ).E ≅ (differenceShortComplex E G φ ψ).homology :=
  Iso.refl _

variable [IsFirstOrderThickening i]

/-- The fixed-endpoint presentation of the descended obstruction sequence. -/
def mapObstructionExtension (E G : ModuleExtension i)
    (φ : E.cokernel ⟶ G.cokernel) (ψ : E.kernel ⟶ G.kernel)
    (hcomm : infinitesimalMap_comm E G φ ψ) :
    CategoryTheory.Extension G.kernel E.cokernel where
  E := (mapObstructionSequence E G φ ψ).X₂
  f := (mapObstructionSequence E G φ ψ).f
  g := (mapObstructionSequence E G φ ψ).g
  zero := (mapObstructionSequence E G φ ψ).zero
  shortExact := mapObstructionSequence_shortExact E G φ ψ hcomm

end AlgebraicGeometry.RingedSpace.Hom.ModuleExtension
