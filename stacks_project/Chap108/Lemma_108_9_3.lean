/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Picard.Relative.Separation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Picard.Relative.LocallyOfFinitePresentation
import StacksCheckRecall

/-!
# Lemma 108.9.3

Under the standing hypotheses of Stacks 108.9, the morphism `Pic_{X/B} ⟶ B` is
quasi-separated and locally of finite presentation.
-/

@[expose]
public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.RelativePicard
open CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.RelativePicard

variable {S : Scheme.{u}} {X B : AlgebraicSpace S}

/- Lemma 108.9.3 (1): with assumptions and notation as in this section
(`f : X ⟶ B` flat, of finite presentation, and proper, and `O_T ⟶ f_{T,*} O_{X_T}`
an isomorphism for every scheme `T` over `B`), the morphism `Pic_{X/B} ⟶ B` is
quasi-separated. Equivalently, the relative diagonal of the Picard functor on
`(Sch/B)` is quasi-compact. -/
@[stacks 0DNI] #check (AlgebraicGeometry.AlgebraicSpace.RelativePicard.quasiSeparated :
    ∀ (f : X ⟶ B)
    [Flat f] [FinitePresentation f] [Proper f]
    [Hom.IsIsoBaseChangeStructurePushforward f],
    IsQuasiCompactOnSchemesOver (Limits.diag (picardFunctor f).obj))

/- Lemma 108.9.3 (2): with the same standing hypotheses, the morphism
`Pic_{X/B} ⟶ B` is locally of finite presentation. -/
@[stacks 0DNI] #check (AlgebraicGeometry.AlgebraicSpace.RelativePicard.isLocallyOfFinitePresentationOver :
    ∀ (f : X ⟶ B)
    [Flat f] [FinitePresentation f] [Proper f]
    [Hom.IsIsoBaseChangeStructurePushforward f],
    IsLocallyOfFinitePresentationOver (picardFunctor f).obj)

/- If the Picard functor is represented by a morphism `π : Y ⟶ B`, then `π` is
quasi-separated. -/
#check (AlgebraicGeometry.AlgebraicSpace.RelativePicard.quasiSeparated_of_representable :
    ∀ (f : X ⟶ B)
    [Flat f] [FinitePresentation f] [Proper f]
    [Hom.IsIsoBaseChangeStructurePushforward f] {Y : AlgebraicSpace S}
    {π : Y ⟶ B} (e : (picardFunctor f).obj ≅ yonedaOver π),
    QuasiSeparated π)

/- If the Picard functor is represented by a morphism `π : Y ⟶ B`, then `π` is
locally of finite presentation. -/
#check (AlgebraicGeometry.AlgebraicSpace.RelativePicard.isLocallyOfFinitePresentationOver_of_representable :
    ∀ (f : X ⟶ B)
    [Flat f] [FinitePresentation f] [Proper f]
    [Hom.IsIsoBaseChangeStructurePushforward f] {Y : AlgebraicSpace S}
    {π : Y ⟶ B} (e : (picardFunctor f).obj ≅ yonedaOver π),
    LocallyOfFinitePresentation π)

end AlgebraicGeometry.AlgebraicSpace.RelativePicard
