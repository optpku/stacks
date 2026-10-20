module

public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.FiberedCategory.Cocartesian
public import ReasLib.AlgebraicGeometry.FormalDeformation.Predeformation
public import ReasLib.CategoryTheory.Fibered.BasedCategory.Basic
public import ReasLib.CategoryTheory.Fibered.BasedCategory.Fiber

/-!
# Predeformation categories from residue-fibre slices

The slice over a residue-fibre object of a category cofibered in groupoids is
again a predeformation category under its forgetful projection.
-/

@[expose] public section

open CategoryTheory ArtinianLocalAlgCat Functor Opposite
open scoped Bicategory

universe u v w

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {F : Type v} [Category.{w} F]

namespace CategoryTheory.Functor

/-- Slicing a category cofibered in groupoids at a residue-fibre object produces a
predeformation category through the forgetful functor from the resulting over category. -/
instance instIsPredeformationCategory_overForget
    (p : F ⥤ ArtinianLocalAlgCat Λ k) [IsFibered.InGroupoids p.op]
    (x : p.Fiber (ArtinianLocalAlgCat.residue Λ k)) :
    IsPredeformationCategory (Over.forget (Fiber.fiberInclusion.obj x) ⋙ p) := by
  have residueHom_eq {baseObject : ArtinianLocalAlgCat Λ k} (first second : baseObject ⟶ residue Λ k) :
      first = second := by
    have homEquality : first.hom = second.hom := by
      apply AlgHom.ext
      intro element
      have firstCompatibility := congrArg
        (fun hom : IsLocalRing.ResidueField baseObject.carrier →ₐ[Λ] k ↦
          hom (IsLocalRing.residue baseObject.carrier element)) first.residue_compat
      have secondCompatibility := congrArg
        (fun hom : IsLocalRing.ResidueField baseObject.carrier →ₐ[Λ] k ↦
          hom (IsLocalRing.residue baseObject.carrier element)) second.residue_compat
      change (residue Λ k).residueFieldIso
        (IsLocalRing.residue k (first.hom element)) = _ at firstCompatibility
      change (residue Λ k).residueFieldIso
        (IsLocalRing.residue k (second.hom element)) = _ at secondCompatibility
      exact (IsLocalRing.residue k).injective
        ((residue Λ k).residueFieldIso.injective
          (firstCompatibility.trans secondCompatibility.symm))
    cases first
    cases second
    cases homEquality
    rename_i firstProof secondProof
    cases firstProof
    cases secondProof
    rfl
  let projection := Over.forget x.1 ⋙ p
  have forgetLift {baseSource baseTarget : ArtinianLocalAlgCat Λ k} {source target : Over x.1}
      {base : baseSource ⟶ baseTarget} {arrow : source ⟶ target}
      (certificate : projection.IsHomLift base arrow) : p.IsHomLift base arrow.left := by
    cases certificate
    exact IsHomLift.map _
  have liftToSlice {baseSource baseTarget : ArtinianLocalAlgCat Λ k} {source target : Over x.1}
      {base : baseSource ⟶ baseTarget} {arrow : source ⟶ target}
      (certificate : p.IsHomLift base arrow.left) : projection.IsHomLift base arrow := by
    exact IsHomLift.of_fac' projection base arrow
      (@IsHomLift.domain_eq _ _ _ _ p _ _ _ _ base arrow.left certificate)
      (@IsHomLift.codomain_eq _ _ _ _ p _ _ _ _ base arrow.left certificate)
      (@IsHomLift.fac' _ _ _ _ p _ _ _ _ base arrow.left certificate)
  have changeCertificate {baseSource baseTarget : ArtinianLocalAlgCat Λ k} {source target : F}
      {base : baseSource ⟶ baseTarget} {arrow : source ⟶ target}
      (certificate : p.IsStronglyCocartesian (p.map arrow) arrow)
      (lift : p.IsHomLift base arrow) : p.IsStronglyCocartesian base arrow := by
    cases lift
    exact certificate
  have changeSliceCertificate {baseSource baseTarget : ArtinianLocalAlgCat Λ k} {source target : Over x.1}
      {base : baseSource ⟶ baseTarget} {arrow : source ⟶ target}
      (certificate : projection.IsStronglyCocartesian (projection.map arrow) arrow)
      (lift : projection.IsHomLift base arrow) : projection.IsStronglyCocartesian base arrow := by
    cases lift
    exact certificate
  have unopLift {baseSource baseTarget : (ArtinianLocalAlgCat Λ k)ᵒᵖ} {source target : Fᵒᵖ}
      {base : baseSource ⟶ baseTarget} {arrow : source ⟶ target}
      (certificate : p.op.IsHomLift base arrow) :
      p.IsHomLift base.unop arrow.unop := by
    cases certificate
    exact IsHomLift.map _
  have opLift {baseSource baseTarget : ArtinianLocalAlgCat Λ k} {source target : F}
      {base : baseSource ⟶ baseTarget} {arrow : source ⟶ target}
      (certificate : p.IsHomLift base arrow) :
      p.op.IsHomLift base.op arrow.op := by
    cases certificate
    exact IsHomLift.map _
  have unopCertificate {baseSource baseTarget : (ArtinianLocalAlgCat Λ k)ᵒᵖ}
      {source target : Fᵒᵖ} {base : baseSource ⟶ baseTarget} {arrow : source ⟶ target}
      (certificate : p.op.IsStronglyCartesian base arrow) :
      p.IsStronglyCocartesian base.unop arrow.unop := by
    refine { toIsHomLift := unopLift certificate.toIsHomLift
             universal_property' := ?_ }
    intro destination nextBase nextArrow nextLift
    have oppositeLift : p.op.IsHomLift (nextBase.op ≫ base) nextArrow.op := by
      simpa only [op_comp, Quiver.Hom.op_unop] using opLift nextLift
    obtain ⟨factor, ⟨factorLift, factorization⟩, uniqueness⟩ :=
      @IsStronglyCartesian.universal_property' _ _ _ _ p.op _ _ _ _
        base arrow certificate (op destination) nextBase.op nextArrow.op oppositeLift
    refine ⟨factor.unop, ⟨unopLift factorLift, congrArg Quiver.Hom.unop factorization⟩, ?_⟩
    intro candidate candidateProperty
    apply Quiver.Hom.op_inj
    exact uniqueness candidate.op
      ⟨opLift candidateProperty.1, congrArg Quiver.Hom.op candidateProperty.2⟩
  have everyArrow {source target : F} (arrow : source ⟶ target) :
      p.IsStronglyCocartesian (p.map arrow) arrow :=
    unopCertificate
      (IsFibered.isStronglyCartesian_of_isCartesian p.op (p.op.map arrow.op) arrow.op)
  have residueLift {source : F} (arrow : source ⟶ x.1) :
      p.IsHomLift (toResidue (p.obj source)) arrow :=
    IsHomLift.of_commsq p _ _ rfl x.2
      (residueHom_eq (p.map arrow ≫ eqToHom x.2) (toResidue (p.obj source)))
  have sliceArrow {source target : Over x.1} (arrow : source ⟶ target) :
      projection.IsStronglyCocartesian (projection.map arrow) arrow := by
    have certificate := everyArrow arrow.left
    refine { universal_property' := ?_ }
    intro destination nextBase nextArrow nextLift
    have underlyingLift : p.IsHomLift (p.map arrow.left ≫ nextBase) nextArrow.left :=
      forgetLift nextLift
    obtain ⟨factor, ⟨factorLift, factorization⟩, uniqueness⟩ :=
      @IsStronglyCocartesian.universal_property' _ _ _ _ p _ _ _ _
        (p.map arrow.left) arrow.left certificate destination.left nextBase
        nextArrow.left underlyingLift
    have square : factor ≫ destination.hom = target.hom := by
      exact @IsStronglyCocartesian.ext _ _ _ _ p _ _ _ _
        (p.map arrow.left) arrow.left certificate _ x.1
        (toResidue (p.obj target.left)) (factor ≫ destination.hom) target.hom
        (residueLift _) (residueLift _)
        (by rw [← Category.assoc, factorization, Over.w, Over.w])
    refine ⟨Over.homMk factor square, ⟨?_, ?_⟩, ?_⟩
    · exact liftToSlice factorLift
    · apply Over.OverMorphism.ext
      exact factorization
    · intro candidate candidateProperty
      apply Over.OverMorphism.ext
      apply uniqueness candidate.left
      exact ⟨forgetLift candidateProperty.1, congrArg Over.Hom.left candidateProperty.2⟩
  have oppositeSlice {baseSource baseTarget : ArtinianLocalAlgCat Λ k}
      {source target : Over x.1} {base : baseSource ⟶ baseTarget} {arrow : source ⟶ target}
      (certificate : projection.IsStronglyCocartesian base arrow) :
      projection.op.IsStronglyCartesian base.op arrow.op := by
    have liftOp {baseSource baseTarget : ArtinianLocalAlgCat Λ k} {source target : Over x.1}
        {base : baseSource ⟶ baseTarget} {arrow : source ⟶ target}
        (certificate : projection.IsHomLift base arrow) :
        projection.op.IsHomLift base.op arrow.op := by
      cases certificate
      exact IsHomLift.map _
    have liftUnop {baseSource baseTarget : (ArtinianLocalAlgCat Λ k)ᵒᵖ}
        {source target : (Over x.1)ᵒᵖ} {base : baseSource ⟶ baseTarget} {arrow : source ⟶ target}
        (certificate : projection.op.IsHomLift base arrow) :
        projection.IsHomLift base.unop arrow.unop := by
      cases certificate
      exact IsHomLift.map _
    refine { toIsHomLift := liftOp certificate.toIsHomLift
             universal_property' := ?_ }
    intro destination nextBase nextArrow nextLift
    have underlyingLift : projection.IsHomLift (base ≫ nextBase.unop) nextArrow.unop := by
      simpa only [unop_comp, Quiver.Hom.unop_op] using liftUnop nextLift
    obtain ⟨factor, ⟨factorLift, factorization⟩, uniqueness⟩ :=
      @IsStronglyCocartesian.universal_property' _ _ _ _ projection _ _ _ _
        base arrow certificate destination.unop nextBase.unop nextArrow.unop underlyingLift
    refine ⟨factor.op, ⟨liftOp factorLift, congrArg Quiver.Hom.op factorization⟩, ?_⟩
    intro candidate candidateProperty
    apply Quiver.Hom.unop_inj
    exact uniqueness candidate.unop
      ⟨liftUnop candidateProperty.1, congrArg Quiver.Hom.unop candidateProperty.2⟩
  have sliceFibered : projection.op.IsFibered := by
    apply IsFibered.of_exists_isStronglyCartesian
    intro source baseObject base
    obtain ⟨destination, arrow, cartesian⟩ :=
      IsPreFibered.exists_isCartesian p.op (a := op source.unop.left) rfl base
    have certificate := unopCertificate
      (@IsFibered.isStronglyCartesian_of_isCartesian _ _ _ _ p.op inferInstance
        _ _ base _ _ arrow cartesian)
    obtain ⟨structureMap, ⟨structureLift, factorization⟩, uniqueness⟩ :=
      @IsStronglyCocartesian.universal_property _ _ _ _ p _ _ _ _
        base.unop arrow.unop certificate _ x.1
        (toResidue baseObject.unop) (toResidue (p.obj source.unop.left))
        (residueHom_eq _ _) source.unop.hom (residueLift _)
    let destinationSlice := Over.mk structureMap
    let sliceHom : source.unop ⟶ destinationSlice := Over.homMk arrow.unop factorization
    have sliceLift : projection.IsHomLift base.unop sliceHom :=
      liftToSlice certificate.toIsHomLift
    refine ⟨op destinationSlice, sliceHom.op, ?_⟩
    exact oppositeSlice (changeSliceCertificate (sliceArrow sliceHom) sliceLift)
  refine { isCofiberedInGroupoids := ?_
           nonempty_residueFiber := ⟨⟨Over.mk (𝟙 x.1), x.2⟩⟩
           unique_residueHom := ?_ }
  · refine { toIsFibered := sliceFibered, all_isCartesian := ?_ }
    intro source target arrow
    exact @IsStronglyCartesian.isCartesian_of_isStronglyCartesian _ _ _ _
      projection.op _ _ _ _ (projection.op.map arrow) arrow
      (oppositeSlice (sliceArrow arrow.unop))
  · intro source target
    have vertical (object : projection.Fiber (residue Λ k)) :
        p.IsHomLift (𝟙 (residue Λ k)) object.1.hom :=
      IsHomLift.of_commsq p _ _ object.2 x.2 (residueHom_eq _ _)
    have targetVertical := vertical target
    have targetCertificate := changeCertificate (everyArrow target.1.hom) targetVertical
    have targetIsIso : IsIso target.1.hom :=
      @IsStronglyCocartesian.isIso_of_base_isIso _ _ _ _ p _ _ _ _
        (𝟙 (residue Λ k)) target.1.hom targetCertificate inferInstance
    have sourceVertical := vertical source
    have inverseLift : p.IsHomLift (𝟙 (residue Λ k)) (CategoryTheory.inv target.1.hom) :=
      @IsHomLift.lift_id_inv_isIso _ _ _ _ p (residue Λ k) _ _
        target.1.hom targetIsIso targetVertical
    let arrow : source.1 ⟶ target.1 :=
      Over.homMk (source.1.hom ≫ CategoryTheory.inv target.1.hom) (by simp)
    have arrowLift : projection.IsHomLift (𝟙 (residue Λ k)) arrow := by
      apply liftToSlice
      exact @IsHomLift.comp_of_lift_id _ _ _ _ p (residue Λ k) _ _ _
        source.1.hom (CategoryTheory.inv target.1.hom) sourceVertical inverseLift
    refine ⟨⟨⟨arrow, arrowLift⟩⟩, ⟨?_⟩⟩
    intro first second
    apply Fiber.hom_ext
    apply Over.OverMorphism.ext
    apply (cancel_mono target.1.hom).1
    exact (Over.w first.1).trans (Over.w second.1).symm

end CategoryTheory.Functor

namespace CategoryTheory.Functor

variable (p : F ⥤ ArtinianLocalAlgCat Λ k) [IsFibered.InGroupoids p.op]

/-- The residue slice of a category cofibered in groupoids at a residue-fibre object is
the forgetful functor from its over-category, composed with the original projection. -/
abbrev sliceAt (x : p.Fiber (residue Λ k)) :
    Over (Fiber.fiberInclusion.obj x) ⥤ ArtinianLocalAlgCat Λ k :=
  Over.forget (Fiber.fiberInclusion.obj x) ⋙ p

/-- The residue slice is the forgetful functor of the over-category at `x`, composed with `p`. -/
theorem sliceAt_def (x : p.Fiber (residue Λ k)) :
    sliceAt p x = Over.forget (Fiber.fiberInclusion.obj x) ⋙ p := sorry

end CategoryTheory.Functor

namespace CategoryTheory.BasedFunctor

variable {G : Type v} [Category.{w} G]
variable {p : F ⥤ ArtinianLocalAlgCat Λ k} {q : G ⥤ ArtinianLocalAlgCat Λ k}
variable [IsFibered.InGroupoids p.op] [IsFibered.InGroupoids q.op]

/-- The residue-fibre image of an object under a based morphism is its image under the
induced functor on the residue fibre. -/
abbrev objAt (φ : BasedCategory.ofFunctor p ⥤ᵇ BasedCategory.ofFunctor q)
    (x : p.Fiber (residue Λ k)) : q.Fiber (residue Λ k) :=
  (φ.fiberFunctor (residue Λ k)).obj x

/-- `objAt φ x` is the image of `x` under the fibre functor of `φ` at the residue field. -/
theorem objAt_def (φ : BasedCategory.ofFunctor p ⥤ᵇ BasedCategory.ofFunctor q)
    (x : p.Fiber (residue Λ k)) :
    objAt φ x = (φ.fiberFunctor (residue Λ k)).obj x := sorry

/-- A based morphism of categories cofibered in groupoids over `ArtinianLocalAlgCat Λ k`
commutes with residue slices after postcomposition on over-categories. -/
theorem sliceMap_w (φ : BasedCategory.ofFunctor p ⥤ᵇ BasedCategory.ofFunctor q)
    (x : p.Fiber (residue Λ k)) :
    Over.post φ.toFunctor ⋙ Functor.sliceAt q (objAt φ x) = Functor.sliceAt p x := sorry

/-- A based morphism induces a based morphism on residue slices by applying its underlying
functor to arrows into the specified residue-fibre object. -/
def sliceMap (φ : BasedCategory.ofFunctor p ⥤ᵇ BasedCategory.ofFunctor q)
    (x : p.Fiber (residue Λ k)) :
    BasedCategory.ofFunctor (Functor.sliceAt p x) ⥤ᵇ
      BasedCategory.ofFunctor (Functor.sliceAt q (objAt φ x)) :=
  BasedFunctor.ofFunctor (Over.post φ.toFunctor) (sliceMap_w φ x)

/-- The underlying functor of `sliceMap φ x` is `Over.post φ.toFunctor`. -/
theorem sliceMap_toFunctor (φ : BasedCategory.ofFunctor p ⥤ᵇ BasedCategory.ofFunctor q)
    (x : p.Fiber (residue Λ k)) :
    (sliceMap φ x).toFunctor = Over.post φ.toFunctor := sorry

end CategoryTheory.BasedFunctor
