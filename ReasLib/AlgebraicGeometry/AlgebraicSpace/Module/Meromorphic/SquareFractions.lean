module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Meromorphic.SquareModule
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Meromorphic.Sheafification

/-! # Genuine fraction pullback into the newly constructed module

On each small square m/s maps to the new module generator divided by
the actual scheme pullback of s. The quotient lift is specified on every
representative; it is not a chosen meromorphic section.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.PullbackFactory Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.MeromorphicConstruction.SquareFractions

open Squares

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [PullbacksMeromorphicFunctionsDefined f] (F : Y.Modules.{u}) (a : Square f)

/-- The denominator and its membership proof use the given pullback property. -/
def denominator (s : (regularStructureSections Y).obj (op ((inclusion Y).obj a.right))) :
    (regularStructureSections X).obj (op ((inclusion X).obj a.left)) :=
  ⟨(SquareModule.coefficient f a).hom s,
    PullbacksMeromorphicFunctionsDefined.pullback_mem_regularStructureSections
      a.geometric s.val s.property⟩

@[simp]
theorem denominator_mul
    (s t : (regularStructureSections Y).obj (op ((inclusion Y).obj a.right))) :
    denominator f a (s * t) = denominator f a s * denominator f a t := by
  apply Subtype.ext
  exact map_mul (SquareModule.coefficient f a).hom s.val t.val

/-- The numerator is the actual geometric/tensor unit image of the given m. -/
def representative
    (p : (Modules.liftModule F).val.obj (op ((inclusion Y).obj a.right)) ×
      (regularStructureSections Y).obj (op ((inclusion Y).obj a.right))) :
    LocalizedModule ((regularStructureSections X).obj (op ((inclusion X).obj a.left)))
      ((Modules.liftModule ((Modules.pullback f).obj F)).val.obj
        (op ((inclusion X).obj a.left))) :=
  LocalizedModule.mk (SquareModule.liftedSection f F a p.1) (denominator f a p.2)

set_option backward.isDefEq.respectTransparency false in
/-- The same annihilating denominator witnesses equivalence after pullback. -/
theorem representative_wd
    (p p' : (Modules.liftModule F).val.obj (op ((inclusion Y).obj a.right)) ×
      (regularStructureSections Y).obj (op ((inclusion Y).obj a.right))) (h : p ≈ p') :
    representative f F a p = representative f F a p' := by
  obtain ⟨c, hc⟩ := h
  apply LocalizedModule.mk_eq.mpr
  refine ⟨denominator f a c, ?_⟩
  have hm := congrArg (SquareModule.liftedSection f F a) hc
  simp only [Submonoid.smul_def] at hm
  rw [SquareModule.liftedSection_smul, SquareModule.liftedSection_smul,
    SquareModule.liftedSection_smul, SquareModule.liftedSection_smul] at hm
  exact hm

/-- Descend that exact representative formula through the localization quotient. -/
def fractionValue
    (z : (meromorphicSectionPresheaf Y F).presheaf.obj
      (op ((inclusion Y).obj a.right))) :
    (meromorphicSectionPresheaf X ((Modules.pullback f).obj F)).presheaf.obj
      (op ((inclusion X).obj a.left)) :=
  LocalizedModule.liftOn z (representative f F a) (representative_wd f F a)

@[simp]
theorem fractionValue_mk
    (m : (Modules.liftModule F).val.obj (op ((inclusion Y).obj a.right)))
    (s : (regularStructureSections Y).obj (op ((inclusion Y).obj a.right))) :
    fractionValue f F a (LocalizedModule.mk m s) =
      LocalizedModule.mk (SquareModule.liftedSection f F a m) (denominator f a s) :=
  LocalizedModule.liftOn_mk (representative_wd f F a) m s

set_option backward.isDefEq.respectTransparency false in
theorem fractionValue_zero : fractionValue f F a 0 = 0 := by
  rw [show (0 : (meromorphicSectionPresheaf Y F).presheaf.obj
    (op ((inclusion Y).obj a.right))) = LocalizedModule.mk 0 1 from
      (LocalizedModule.zero_mk 1).symm]
  rw [fractionValue_mk, SquareModule.liftedSection_zero, LocalizedModule.zero_mk]

set_option backward.isDefEq.respectTransparency false in
theorem fractionValue_add
    (z w : (meromorphicSectionPresheaf Y F).presheaf.obj
      (op ((inclusion Y).obj a.right))) :
    fractionValue f F a (z + w) = fractionValue f F a z + fractionValue f F a w := by
  induction z, w using LocalizedModule.induction_on₂ with
  | h m n s t =>
    rw [LocalizedModule.mk_add_mk, fractionValue_mk, fractionValue_mk, fractionValue_mk,
      LocalizedModule.mk_add_mk]
    simp only [Submonoid.smul_def, denominator_mul]
    rw [SquareModule.liftedSection_add,
      SquareModule.liftedSection_smul, SquareModule.liftedSection_smul]
    rfl

/-- The actual quotient map, with the additive laws above proved. -/
def fractionMap :
    (meromorphicSectionPresheaf Y F).presheaf.obj (op ((inclusion Y).obj a.right)) ⟶
      (meromorphicSectionPresheaf X ((Modules.pullback f).obj F)).presheaf.obj
        (op ((inclusion X).obj a.left)) :=
  AddCommGrpCat.ofHom
    { toFun := fractionValue f F a
      map_zero' := fractionValue_zero f F a
      map_add' := fractionValue_add f F a }

/-- Sheafify the actual fraction using the previously proved coefficient-size certificate. -/
def sheafMap :
    (meromorphicSectionPresheaf Y F).presheaf.obj (op ((inclusion Y).obj a.right)) ⟶
      ((SheafOfModules.toSheaf _).obj
        (meromorphicSectionSheaf X ((Modules.pullback f).obj F))).obj.obj
        (op ((inclusion X).obj a.left)) := by
  -- Local instance justification (defeq pin): Use the named additive sheafification adjunction at X to identify the specified localization sheaf and its unit.
  letI := Sheafification.additiveCertificate X
  exact fractionMap f F a ≫
    (toSheafify (smallEtaleTopology X)
      (meromorphicSectionPresheaf X ((Modules.pullback f).obj F)).presheaf).app
        (op ((inclusion X).obj a.left))

end AlgebraicGeometry.AlgebraicSpace.MeromorphicConstruction.SquareFractions
