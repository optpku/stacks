module

public import ReasLib.RingTheory.RingHom.IndZariski
import StacksCheckRecall

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits

/- Lemma 61.4.5: a filtered colimit of ind-Zariski A-algebras is ind-Zariski
over A. Canonical owner: `RingHom.IndZariski.of_isColimit`. -/
@[stacks 096S] #check (RingHom.IndZariski.of_isColimit :
  ∀ {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    {J : Type v} [Category.{v} J] [IsFiltered J]
    (F : J ⥤ Under (CommRingCat.of R))
    (c : Cocone F)
    (hc : IsColimit c)
    (e : c.pt ≅ Under.mk (CommRingCat.ofHom (algebraMap R A)))
    (hF : ∀ j, (CommRingCat.Hom.hom (F.obj j).hom).IndZariski),
    (algebraMap R A).IndZariski)
