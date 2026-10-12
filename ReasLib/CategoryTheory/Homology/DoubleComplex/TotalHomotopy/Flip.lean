/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Homology.DoubleComplex.TotalHomotopy
public import ReasLib.CategoryTheory.Homology.DoubleComplex.TotalSymmetry

/-!
# Totalization of homotopies in the second direction

Second-direction homotopies are first-direction homotopies after flipping a double complex.
This file transports the generic total-homotopy API across the canonical symmetry of total
complexes.
-/

@[expose] public section

open CategoryTheory ComplexShape HomologicalComplex HomotopyCategory

noncomputable section

universe v u

namespace HomologicalComplex₂

namespace Total.Homotopy.Second

variable {C : Type u} [Category.{v} C] [Preadditive C]
variable {K L : HomologicalComplex₂ C (up ℤ) (up ℤ)}
variable [K.HasTotal (up ℤ)] [L.HasTotal (up ℤ)]

/-- The degree-`q` comparison between flipping a second-direction shift and shifting the flipped
double complex. -/
noncomputable def flipSecondShiftComponent
    (M : HomologicalComplex₂ C (up ℤ) (up ℤ)) (n q : ℤ) :
    ((flipFunctor C (up ℤ) (up ℤ)).obj ((shiftFunctor₂ C n).obj M)).X q ≅
      (M.flip⟦n⟧).X q :=
  Iso.refl _

/-- The flip/second-shift comparison components commute with the outer differentials. -/
theorem flipSecondShiftComponentComm
    (M : HomologicalComplex₂ C (up ℤ) (up ℤ)) (n q q' : ℤ)
    (hqq' : (up ℤ).Rel q q') :
    (flipSecondShiftComponent M n q).hom ≫ (M.flip⟦n⟧).d q q' =
      ((flipFunctor C (up ℤ) (up ℤ)).obj ((shiftFunctor₂ C n).obj M)).d q q' ≫
        (flipSecondShiftComponent M n q').hom := sorry

/-- The canonical isomorphism from the flip of a second-direction shift to the ordinary shift
of the flipped double complex. -/
@[stacks 0G6A "flip/second-shift comparison"]
noncomputable def flipSecondShiftIso
    (M : HomologicalComplex₂ C (up ℤ) (up ℤ)) (n : ℤ) :
    (flipFunctor C (up ℤ) (up ℤ)).obj ((shiftFunctor₂ C n).obj M) ≅ M.flip⟦n⟧ :=
  HomologicalComplex.Hom.isoOfComponents
    (flipSecondShiftComponent M n)
    (flipSecondShiftComponentComm M n)

/-- Conjugating the total of a flipped map by the total-flip comparisons recovers the original
total map. -/
theorem flip_naturality (f : K ⟶ L) :
    ((K.totalFlipIso (up ℤ)).inv ≫
        total.map ((flipFunctor C (up ℤ) (up ℤ)).map f) (up ℤ)) ≫
          (L.totalFlipIso (up ℤ)).hom =
      total.map f (up ℤ) := sorry

/-- A homotopy in the second direction induces a homotopy of total-complex maps. -/
@[stacks 0G6A]
noncomputable def of {f g : K ⟶ L}
    (h : Homotopy ((flipFunctor C (up ℤ) (up ℤ)).map f)
      ((flipFunctor C (up ℤ) (up ℤ)).map g)) :
    Homotopy (total.map f (up ℤ)) (total.map g (up ℤ)) :=
  (Homotopy.ofEq (flip_naturality f).symm).trans
    ((((First.of h).compLeft (K.totalFlipIso (up ℤ)).inv).compRight
      (L.totalFlipIso (up ℤ)).hom).trans
        (Homotopy.ofEq (flip_naturality g)))

/-- Maps homotopic in the second direction induce homotopic total maps. -/
@[stacks 0G6A]
theorem homotopic {f g : K ⟶ L}
    (h : Homotopy ((flipFunctor C (up ℤ) (up ℤ)).map f)
      ((flipFunctor C (up ℤ) (up ℤ)).map g)) :
    homotopic C (up ℤ) (total.map f (up ℤ)) (total.map g (up ℤ)) := sorry

/-- Maps homotopic in the second direction induce equal maps between total complexes in the
homotopy category. -/
@[stacks 0G6A]
theorem map_eq_in_homotopyCategory {f g : K ⟶ L}
    (h : Homotopy ((flipFunctor C (up ℤ) (up ℤ)).map f)
      ((flipFunctor C (up ℤ) (up ℤ)).map g)) :
    (quotient C (up ℤ)).map (total.map f (up ℤ)) =
      (quotient C (up ℤ)).map (total.map g (up ℤ)) := sorry

/-- Flipping a second-direction shift gives the ordinary shift of the flipped double complex. -/
theorem flip_secondShift (M : HomologicalComplex₂ C (up ℤ) (up ℤ)) (n : ℤ) :
    (flipFunctor C (up ℤ) (up ℤ)).obj ((shiftFunctor₂ C n).obj M) = M.flip⟦n⟧ := sorry

/-- A map between flipped double complexes with shifted target determines a map to the
corresponding second-direction bidegree shift before flipping. -/
noncomputable def fromFlipToShift (n : ℤ)
    (f : K.flip ⟶ L.flip⟦n⟧) : K ⟶ L.bidegreeShift 0 n :=
  (flipEquivalence C (up ℤ) (up ℤ)).functor.preimage
      (f ≫ (flipSecondShiftIso L n).inv) ≫
    (shiftFunctorZero (HomologicalComplex₂ C (up ℤ) (up ℤ)) ℤ).inv.app
      ((shiftFunctor₂ C n).obj L)

namespace FromFlipToShift

/-- Transport a raw component family on flipped shifted double complexes to the corresponding
second-direction bidegree-shift components before flipping. -/
@[stacks 0G6A "unflip shifted bidegree components"]
noncomputable def componentOf (n : ℤ)
    (f : ∀ q p : ℤ, (K.flip.X q).X p ⟶ (L.flip⟦n⟧.X q).X p) (p q : ℤ) :
    (K.X p).X q ⟶ ((L.bidegreeShift 0 n).X p).X q :=
  f q p ≫
    (CochainComplex.shiftFunctorObjXIso L.flip n q (q + n) rfl).hom.f p ≫
      (L.shiftFunctor₂XXIso p q n (q + n) rfl).inv ≫
        (((shiftFunctor₂ C n).obj L).shiftFunctor₁XXIso p 0 p
          (Int.add_zero p).symm q).inv

/-- The bidegree `(p,q)` component of the map obtained by unflipping a shifted target. -/
noncomputable def component (n : ℤ)
    (f : K.flip ⟶ L.flip⟦n⟧) (p q : ℤ) :
    (K.X p).X q ⟶ ((L.bidegreeShift 0 n).X p).X q :=
  componentOf n (fun q p ↦ (f.f q).f p) p q

/-- The packaged unflip map has the raw bidegree component exposed by `component`. -/
theorem component_eq
    (n : ℤ) (f : K.flip ⟶ L.flip⟦n⟧) (p q : ℤ) :
    ((fromFlipToShift n f).f p).f q = component n f p q := sorry

end FromFlipToShift

/-- Under the self-homotopy-to-shift identification, totalization in the second direction
agrees with the second-direction bidegree-shift comparison, including its Koszul sign. -/
@[stacks 0G6A]
theorem selfHomotopyToShift
    {f : K ⟶ L}
    (h : Homotopy ((flipFunctor C (up ℤ) (up ℤ)).map f)
      ((flipFunctor C (up ℤ) (up ℤ)).map f)) :
    CochainComplex.Homotopy.selfEquivShiftHom (total.map f (up ℤ))
        (of h) =
      total.map
          (fromFlipToShift (-1)
            (CochainComplex.Homotopy.selfEquivShiftHom
              ((flipFunctor C (up ℤ) (up ℤ)).map f) h))
          (up ℤ) ≫
        (BidegreeShift.totalIso L 0 (-1)).hom := sorry

end Total.Homotopy.Second

end HomologicalComplex₂
