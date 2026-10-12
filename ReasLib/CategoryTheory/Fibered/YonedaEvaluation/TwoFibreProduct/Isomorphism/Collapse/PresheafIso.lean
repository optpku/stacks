/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.YonedaEvaluation.TwoFibreProduct.Isomorphism.Collapse.Equivalence
public import ReasLib.CategoryTheory.Fibered.FiberIsoClassPresheaf.Equivalence.QuasiInverse

/-!
# The presheaf comparison induced by collapse

This leaf identifies the lifted isomorphism presheaf with fibrewise isomorphism classes in the
literal two-fibre-product source.
-/

@[expose] public section

universe u v

namespace CategoryTheory

open Opposite CategoryOfElements
open scoped Bicategory BasedFunctor

variable {C : Type u} [Category.{v} C]

namespace FiberedCategoryOver.TwoFibreProduct.Isomorphism

variable (X : FiberedCategoryOver C) {U : C} (x y : X.p.Fiber U)

namespace collapse
namespace sourcePresheafIso

/-- A supplied collapse quasi-inverse identifies the literal source class presheaf with the
size-stable canonical isomorphism presheaf. This explicit-data variant is useful when a downstream
construction must retain its own unit and counit choices. -/
noncomputable def ofQuasiInverse
    (e : BasedFunctor.QuasiInverse (collapse X x y)) :
    presheafULift X x y ≅
      Functor.fiberIsoClassPresheaf (sourceSetoids X x y).p :=
  presheafULift.fiberObjectIso X x y ≪≫
    e.fiberClassesIso.symm

namespace ofQuasiInverse.hom

/-- Pointwise, the forward source-presheaf comparison reconstructs a literal source object with
the supplied inverse and then takes its fibrewise isomorphism class. -/
@[simp]
theorem app
    (e : BasedFunctor.QuasiInverse (collapse X x y)) (A : (Over U)ᵒᵖ)
    (s : (presheafULift X x y).obj A) :
    (ofQuasiInverse X x y e).hom.app A s =
      Quotient.mk''
        ((e.inverse.fiberFunctor (unop A)).obj
          (FiberedCategoryOver.Sets.ofPresheaf.valueToFiber
            (presheafULift X x y) (unop A) s)) := sorry

end ofQuasiInverse.hom

namespace ofQuasiInverse.inv

/-- Pointwise, the inverse source-presheaf comparison collapses a represented literal source
object and then reads it as a section of the canonical isomorphism presheaf. -/
@[simp]
theorem app_mk
    (e : BasedFunctor.QuasiInverse (collapse X x y)) (A : (Over U)ᵒᵖ)
    (Q : (sourceSetoids X x y).p.Fiber (unop A)) :
    (ofQuasiInverse X x y e).inv.app A (Quotient.mk'' Q) =
      FiberedCategoryOver.Sets.ofPresheaf.fiberToValue
        (presheafULift X x y) (unop A)
        (((collapse X x y).fiberFunctor (unop A)).obj Q) := sorry

end ofQuasiInverse.inv
end sourcePresheafIso

/-- Lemma 8.2.5 (2): the canonical comparison between the value-universe-normalized isomorphism
presheaf and fibrewise isomorphism classes in the literal two-fibre-product source. -/
@[stacks 04SI "(2)"]
noncomputable def sourcePresheafIso :
    presheafULift X x y ≅
      Functor.fiberIsoClassPresheaf (sourceSetoids X x y).p :=
  sourcePresheafIso.ofQuasiInverse X x y (quasiInverse X x y)

namespace sourcePresheafIso

/-- The source-presheaf comparison is independent of the supplied collapse coherence package.
This is the collapse specialization of
`BasedFunctor.QuasiInverse.fiberClassesIso.eq`. -/
theorem eq_ofQuasiInverse
    (e : BasedFunctor.QuasiInverse (collapse X x y)) :
    collapse.sourcePresheafIso X x y = ofQuasiInverse X x y e := sorry

namespace hom

/-- Pointwise, the canonical source-presheaf comparison reconstructs the deterministic literal
source representative and takes its fibrewise isomorphism class. -/
@[simp]
theorem app (A : (Over U)ᵒᵖ) (s : (presheafULift X x y).obj A) :
    (collapse.sourcePresheafIso X x y).hom.app A s =
      Quotient.mk''
        (((collapse.inverse X x y).fiberFunctor (unop A)).obj
          (FiberedCategoryOver.Sets.ofPresheaf.valueToFiber
            (presheafULift X x y) (unop A) s)) := sorry

end hom

namespace inv

/-- Pointwise, the inverse canonical source-presheaf comparison collapses a represented literal
source object to its canonical isomorphism section. -/
theorem app_mk (A : (Over U)ᵒᵖ)
    (Q : (sourceSetoids X x y).p.Fiber (unop A)) :
    (collapse.sourcePresheafIso X x y).inv.app A (Quotient.mk'' Q) =
      FiberedCategoryOver.Sets.ofPresheaf.fiberToValue
        (presheafULift X x y) (unop A)
        (((collapse X x y).fiberFunctor (unop A)).obj Q) := sorry

/-- The inverse source-presheaf comparison is the collapsed isomorphism section, transported
along the equality that places the literal source object in the displayed fibre. -/
@[simp]
theorem app_mk_ulift (A : (Over U)ᵒᵖ)
    (Q : (sourceSetoids X x y).p.Fiber (unop A)) :
    (collapse.sourcePresheafIso X x y).inv.app A (Quotient.mk'' Q) =
      (presheafULift X x y).map (eqToHom (congrArg op Q.2))
        (isomSection.ulift X x y Q.1) := sorry

end inv
end sourcePresheafIso
end collapse
end FiberedCategoryOver.TwoFibreProduct.Isomorphism
end CategoryTheory
