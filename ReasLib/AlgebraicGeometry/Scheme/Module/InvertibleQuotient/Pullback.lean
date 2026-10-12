/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Invertible.Pullback
public import ReasLib.CategoryTheory.Monoidal.InvertibleQuotient.IsoClass

/-!
# Pullback of invertible quotients

Invertible quotients of scheme modules and their compatible-isomorphism classes
pull back along morphisms of schemes.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace CategoryTheory.InvertibleQuotient

variable {X Y Z : Scheme.{u}}

/-- Pullback preserves epimorphic quotient maps of scheme modules. -/
theorem pullbackMap_epi (f : X ⟶ Y) {E : Y.Modules}
    (q : InvertibleQuotient E) :
    Epi ((Scheme.Modules.pullback f).map q.hom) := sorry

/-- Pulling back an invertible quotient gives an invertible quotient of the pulled-back
source module. -/
noncomputable def pullback (f : X ⟶ Y) {E : Y.Modules}
    (q : InvertibleQuotient E) :
    InvertibleQuotient ((Scheme.Modules.pullback f).obj E) where
  object := (Scheme.Modules.pullback f).obj q.object
  isInvertible := Scheme.Modules.Invertible.pullback f q.isInvertible
  hom := (Scheme.Modules.pullback f).map q.hom
  hom_epi := pullbackMap_epi f q

/-- Pullback preserves compatible target isomorphisms between invertible quotients. -/
theorem pullback_rel (f : X ⟶ Y) {E : Y.Modules}
    {q q' : InvertibleQuotient E} (h : Rel q q') :
    Rel (pullback f q) (pullback f q') := sorry

/-- Pullback of invertible quotients descends to compatible-isomorphism classes. -/
noncomputable def pullbackClass (f : X ⟶ Y) {E : Y.Modules} :
    IsoClass E → IsoClass ((Scheme.Modules.pullback f).obj E) :=
  Quotient.map (pullback f) (fun _ _ ↦ pullback_rel f)

/-- Pullback after source transport preserves compatible target isomorphism. -/
theorem pullbackAlong_rel (f : X ⟶ Y) {E E' : Y.Modules} (e : E ≅ E')
    {q q' : InvertibleQuotient E'} (h : Rel q q') :
    Rel (pullback f (precomposeIso e q))
      (pullback f (precomposeIso e q')) := sorry

/-- Pullback along the identity agrees, up to source transport, with the original quotient
class. -/
theorem pullbackAlong_id_rel {E : X.Modules} (q : IsoClass E) :
    pullbackClass (𝟙 X) q =
      precomposeIsoClass ((Scheme.Modules.pullbackId X).app E) q := sorry

/-- Successive pullbacks agree with pullback along the composite, after the canonical source
comparison. -/
theorem pullbackAlong_comp_rel (f : X ⟶ Y) (g : Y ⟶ Z) {E : Z.Modules}
    (q : IsoClass E) :
    pullbackClass f (pullbackClass g q) =
      precomposeIsoClass ((Scheme.Modules.pullbackComp f g).app E)
        (pullbackClass (f ≫ g) q) := sorry

end CategoryTheory.InvertibleQuotient
