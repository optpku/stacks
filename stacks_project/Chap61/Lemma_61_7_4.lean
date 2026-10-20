/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.RingHom.IndEtale.Colimit
import StacksCheckRecall

@[expose] public section

open CategoryTheory Limits

universe u v

/- Lemma 61.7.4: a filtered colimit of ind-étale A-algebras is ind-étale
over A. Canonical owner: `RingHom.IndEtale.of_isColimit`. -/
@[stacks 097L] #check (RingHom.IndEtale.of_isColimit :
  ∀ {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    {J : Type v} [Category.{v} J] [IsFiltered J]
    (F : J ⥤ Under (CommRingCat.of R)) (c : Cocone F) (hc : IsColimit c)
    (e : c.pt ≅ Under.mk (CommRingCat.ofHom (algebraMap R A)))
    (hF : ∀ j, ((F.obj j).hom.hom).IndEtale),
    (algebraMap R A).IndEtale)
