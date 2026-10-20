/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Coproduct
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits Opposite

universe u v

/- Lemma 65.8.4: for a scheme `S` and a family of algebraic spaces `F i` indexed by
`[Small.{u} I]`, the sheaf coproduct is an algebraic space. Surjective étale scheme
atlases `U i ⟶ F i` give a surjective étale atlas from their coproduct in `Over S`.
The universe bound ensures that this scheme coproduct is an object of `Over S`. -/
@[stacks 02WQ] #check (AlgebraicGeometry.AlgebraicSpace.coproduct :
  {S : Scheme.{u}} → {I : Type v} → [Small.{u} I] →
    (I → AlgebraicSpace S) → AlgebraicSpace S)

#check (AlgebraicGeometry.AlgebraicSpace.coproduct_functorOfPoints :
  ∀ {S : Scheme.{u}} {I : Type v} [Small.{u} I] (F : I → AlgebraicSpace S),
    (AlgebraicSpace.coproduct F).functorOfPoints = AlgebraicSpace.coproductSheaf F)

#check (AlgebraicGeometry.AlgebraicSpace.coproductSheaf_universal :
  ∀ {S : Scheme.{u}} {I : Type v} [Small.{u} I] (F : I → AlgebraicSpace S)
    (P : (Over S)ᵒᵖ ⥤ Type u), Presheaf.IsSheaf (Scheme.fppfTopology.over S) P →
    ∀ p : ∀ i, (F i).functorOfPoints ⟶ P,
      ∃! q : AlgebraicSpace.coproductSheaf F ⟶ P,
        ∀ i, NatTrans.vcomp (AlgebraicSpace.coproductι F i) q = p i)

#check (AlgebraicGeometry.AlgebraicSpace.coproduct_of_etale_atlas :
  ∀ {S : Scheme.{u}} {I : Type v} [Small.{u} I] (F : I → AlgebraicSpace S)
    {U : I → Over S} (p : ∀ i, yoneda.obj (U i) ⟶ (F i).functorOfPoints),
    (∀ i, (MorphismProperty.over (@Etale)).presheaf (p i)) →
    (∀ i, Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) (p i)) →
      (MorphismProperty.over (@Etale)).presheaf (AlgebraicSpace.coproductEtaleAtlas F p) ∧
        Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S)
          (AlgebraicSpace.coproductEtaleAtlas F p))
