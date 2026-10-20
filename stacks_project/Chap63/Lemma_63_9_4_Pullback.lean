module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.CommSq
public import ReasLib.AlgebraicGeometry.Scheme.Compactification.FixedInterior
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType
public import stacks_project.Chap63.Lemma_63_9_2_Compactification

/-!
# Base-changed compactifications for derived étale lower shriek

Given a cartesian square of qcqs schemes with `f` separated of finite type and
a compactification of `f`, form the base-changed compactification of `f'`
used to compare `Rf_!` with `Rf'_!`.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Compactification

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale
namespace etaleDerivedLowerShriek

variable {X Y X' Y' : Scheme.{u}}

/-- The over-object for `f` has the same underlying morphism as `f`. -/
instance instIsSeparated_overMk (f : X ⟶ Y) [IsSeparated f] :
    IsSeparated (Over.mk f).hom :=
  inferInstanceAs (IsSeparated f)

/-- Finite type of `f` transfers to `Over.mk f`. -/
instance instFiniteType_overMk (f : X ⟶ Y) [Scheme.Hom.FiniteType f] :
    Scheme.Hom.FiniteType (Over.mk f).hom :=
  inferInstanceAs (Scheme.Hom.FiniteType f)

/-- Quasi-compactness of `X` transfers to the source of `Over.mk f`. -/
instance instCompactSpace_overMk_left (f : X ⟶ Y) [CompactSpace X] :
    CompactSpace (Over.mk f).left :=
  inferInstanceAs (CompactSpace X)

/-- The interior immersion of a compactification is étale. -/
instance instEtale_ι (f : X ⟶ Y) (P : Of Y (Over.mk f)) :
    Etale (Of.ι P) :=
  inferInstance

/-- The interior immersion of a compactification is separated. -/
instance instIsSeparated_ι (f : X ⟶ Y) (P : Of Y (Over.mk f)) :
    IsSeparated (Of.ι P) :=
  sorry

/-- The interior immersion of a compactification is locally quasi-finite. -/
instance instLocallyQuasiFinite_ι (f : X ⟶ Y) (P : Of Y (Over.mk f)) :
    LocallyQuasiFinite (Of.ι P) :=
  sorry

/-- The interior immersion of a compactification is locally of finite type. -/
instance instLocallyOfFiniteType_ι (f : X ⟶ Y) (P : Of Y (Over.mk f)) :
    LocallyOfFiniteType (Of.ι P) :=
  sorry

/-- Quasi-separatedness of `X` transfers to the source of `Over.mk f`. -/
instance instQuasiSeparatedSpace_overMk_left (f : X ⟶ Y)
    [QuasiSeparatedSpace X] :
    QuasiSeparatedSpace (Over.mk f).left :=
  inferInstanceAs (QuasiSeparatedSpace X)

/-- Cartesian base change of a separated morphism is separated. -/
theorem isSeparated_f' (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y')
    (g' : X' ⟶ X) (h_cart : IsPullback g' f' f g) [IsSeparated f] :
    IsSeparated f' :=
  sorry

/-- Cartesian base change of a finite-type morphism is of finite type. -/
theorem finiteType_f' (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y')
    (g' : X' ⟶ X) (h_cart : IsPullback g' f' f g) [Scheme.Hom.FiniteType f] :
    Scheme.Hom.FiniteType f' :=
  sorry

/-- The over-object for `f'` has the same underlying morphism as `f'`. -/
instance instIsSeparated_overMk_f' (f' : X' ⟶ Y') [IsSeparated f'] :
    IsSeparated (Over.mk f').hom :=
  inferInstanceAs (IsSeparated f')

/-- Finite type of `f'` transfers to `Over.mk f'`. -/
instance instFiniteType_overMk_f' (f' : X' ⟶ Y') [Scheme.Hom.FiniteType f'] :
    Scheme.Hom.FiniteType (Over.mk f').hom :=
  inferInstanceAs (Scheme.Hom.FiniteType f')

/-- Quasi-compactness of `X'` transfers to the source of `Over.mk f'`. -/
instance instCompactSpace_overMk_f'_left (f' : X' ⟶ Y') [CompactSpace X'] :
    CompactSpace (Over.mk f').left :=
  inferInstanceAs (CompactSpace X')

/-- Quasi-separatedness of `X'` transfers to the source of `Over.mk f'`. -/
instance instQuasiSeparatedSpace_overMk_f'_left (f' : X' ⟶ Y')
    [QuasiSeparatedSpace X'] :
    QuasiSeparatedSpace (Over.mk f').left :=
  inferInstanceAs (QuasiSeparatedSpace X')

/-- The ambient scheme `X̄'` of the base-changed compactification, the fibre
product of `g` and the structure map of `P`. -/
def ambient (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X)
    (h_cart : IsPullback g' f' f g) (P : Of Y (Over.mk f)) : Scheme.{u} :=
  pullback g P.obj.right.hom

/-- The structure map `f̄' : X̄' ⟶ Y'` of the base-changed compactification. -/
def ambientToBase (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X)
    (h_cart : IsPullback g' f' f g) (P : Of Y (Over.mk f)) :
    ambient f g f' g' h_cart P ⟶ Y' :=
  pullback.fst g P.obj.right.hom

/-- The base change `ḡ' : X̄' ⟶ X̄` of the compactification ambient. -/
def ambientToSource (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X)
    (h_cart : IsPullback g' f' f g) (P : Of Y (Over.mk f)) :
    ambient f g f' g' h_cart P ⟶ P.obj.right.left :=
  pullback.snd g P.obj.right.hom

/-- The compactification triangle `j ≫ f̄ = f`. -/
theorem interior_triangle (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y')
    (g' : X' ⟶ X) (h_cart : IsPullback g' f' f g) (P : Of Y (Over.mk f)) :
    Of.ι P ≫ P.obj.right.hom = f :=
  Over.w P.obj.hom

/-- The lift witness `f' ≫ g = (g' ≫ j) ≫ f̄` for the interior of the
base-changed compactification. -/
theorem interior_fac (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X)
    (h_cart : IsPullback g' f' f g) (P : Of Y (Over.mk f)) :
    (g' ≫ Of.ι P) ≫ P.obj.right.hom = f' ≫ g :=
  (Category.assoc g' (Of.ι P) P.obj.right.hom).symm.trans
    ((congrArg (fun h ↦ g' ≫ h)
        (interior_triangle f g f' g' h_cart P)).trans h_cart.w)

/-- The ambient square of the chosen compactification is the defining pullback
of `g` and `f̄`. -/
def ambient_isPullback (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X)
    (h_cart : IsPullback g' f' f g) (P : Of Y (Over.mk f)) :
    IsPullback (ambientToSource f g f' g' h_cart P)
      (ambientToBase f g f' g' h_cart P) P.obj.right.hom g :=
  (IsPullback.of_hasPullback g P.obj.right.hom).flip

/-- The interior immersion `j' : X' ⟶ X̄'` induced by the cartesian square and
the compactification triangle. -/
def interiorLift (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X)
    (h_cart : IsPullback g' f' f g) (P : Of Y (Over.mk f)) :
    X' ⟶ ambient f g f' g' h_cart P :=
  (ambient_isPullback f g f' g' h_cart P).lift (g' ≫ Of.ι P) f'
    (interior_fac f g f' g' h_cart P)

/-- The triangle `j' ≫ f̄' = f'`. -/
theorem interiorLift_comp_toBase (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y')
    (g' : X' ⟶ X) (h_cart : IsPullback g' f' f g) (P : Of Y (Over.mk f)) :
    interiorLift f g f' g' h_cart P ≫ ambientToBase f g f' g' h_cart P = f' :=
  IsPullback.lift_snd (ambient_isPullback f g f' g' h_cart P) (g' ≫ Of.ι P) f'
    (interior_fac f g f' g' h_cart P)

/-- The triangle `j' ≫ ḡ' = g' ≫ j`. -/
theorem interiorLift_comp_toSource (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y')
    (g' : X' ⟶ X) (h_cart : IsPullback g' f' f g) (P : Of Y (Over.mk f)) :
    interiorLift f g f' g' h_cart P ≫ ambientToSource f g f' g' h_cart P =
      g' ≫ Of.ι P :=
  IsPullback.lift_fst (ambient_isPullback f g f' g' h_cart P) (g' ≫ Of.ι P) f'
    (interior_fac f g f' g' h_cart P)

/-- The interior square of the compactification cube is cartesian. -/
theorem interior_isPullback (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X)
    (h_cart : IsPullback g' f' f g) (P : Of Y (Over.mk f)) :
    IsPullback g' (interiorLift f g f' g' h_cart P) (Of.ι P)
      (ambientToSource f g f' g' h_cart P) :=
  IsPullback.of_bot'
    ((interior_triangle f g f' g' h_cart P).symm ▸ h_cart)
    (ambient_isPullback f g f' g' h_cart P)

/-- The induced interior `j'` is an open immersion. -/
instance instIsOpenImmersion_interiorLift (f : X ⟶ Y) (g : Y' ⟶ Y)
    (f' : X' ⟶ Y') (g' : X' ⟶ X) (h_cart : IsPullback g' f' f g)
    (P : Of Y (Over.mk f)) :
    IsOpenImmersion (interiorLift f g f' g' h_cart P) :=
  sorry

/-- The induced interior `j'` is quasi-compact. -/
instance instQuasiCompact_interiorLift (f : X ⟶ Y) (g : Y' ⟶ Y)
    (f' : X' ⟶ Y') (g' : X' ⟶ X) (h_cart : IsPullback g' f' f g)
    (P : Of Y (Over.mk f)) :
    QuasiCompact (interiorLift f g f' g' h_cart P) :=
  sorry

/-- The induced interior `j'` is étale. -/
instance instEtale_interiorLift (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y')
    (g' : X' ⟶ X) (h_cart : IsPullback g' f' f g) (P : Of Y (Over.mk f)) :
    Etale (interiorLift f g f' g' h_cart P) :=
  sorry

/-- The induced interior `j'` is separated. -/
instance instIsSeparated_interiorLift (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y')
    (g' : X' ⟶ X) (h_cart : IsPullback g' f' f g) (P : Of Y (Over.mk f)) :
    IsSeparated (interiorLift f g f' g' h_cart P) :=
  sorry

/-- The induced interior `j'` is locally quasi-finite. -/
instance instLocallyQuasiFinite_interiorLift (f : X ⟶ Y) (g : Y' ⟶ Y)
    (f' : X' ⟶ Y') (g' : X' ⟶ X) (h_cart : IsPullback g' f' f g)
    (P : Of Y (Over.mk f)) :
    LocallyQuasiFinite (interiorLift f g f' g' h_cart P) :=
  sorry

/-- The induced interior `j'` is locally of finite type. -/
instance instLocallyOfFiniteType_interiorLift (f : X ⟶ Y) (g : Y' ⟶ Y)
    (f' : X' ⟶ Y') (g' : X' ⟶ X) (h_cart : IsPullback g' f' f g)
    (P : Of Y (Over.mk f)) :
    LocallyOfFiniteType (interiorLift f g f' g' h_cart P) :=
  sorry

/-- The structure map `f̄'` is proper, as a base change of the proper ambient
map of `P`. -/
instance instIsProper_ambientToBase (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y')
    (g' : X' ⟶ X) (h_cart : IsPullback g' f' f g) (P : Of Y (Over.mk f)) :
    IsProper (ambientToBase f g f' g' h_cart P) :=
  sorry

/-- The ambient of the base-changed compactification is quasi-compact. -/
instance instCompactSpace_ambient (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y')
    (g' : X' ⟶ X) (h_cart : IsPullback g' f' f g) (P : Of Y (Over.mk f)) :
    CompactSpace (ambient f g f' g' h_cart P) :=
  sorry

/-- The ambient of the base-changed compactification is quasi-separated. -/
instance instQuasiSeparatedSpace_ambient (f : X ⟶ Y) (g : Y' ⟶ Y)
    (f' : X' ⟶ Y') (g' : X' ⟶ X) (h_cart : IsPullback g' f' f g)
    (P : Of Y (Over.mk f)) :
    QuasiSeparatedSpace (ambient f g f' g' h_cart P) :=
  sorry

/-- Compactification of `f'` obtained by base-changing the interior and
ambient of `P`. -/
def compactificationPullback (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y')
    (g' : X' ⟶ X) (h_cart : IsPullback g' f' f g) (P : Of Y (Over.mk f)) :
    Of Y' (Over.mk f') :=
  @Of.mk Y' (Over.mk f') (Over.mk (ambientToBase f g f' g' h_cart P))
    (Over.homMk (interiorLift f g f' g' h_cart P)
      (interiorLift_comp_toBase f g f' g' h_cart P))
    (instIsOpenImmersion_interiorLift f g f' g' h_cart P)
    (instQuasiCompact_interiorLift f g f' g' h_cart P)
    (instIsProper_ambientToBase f g f' g' h_cart P)

/-- The interior immersion of the base-changed compactification is `j'`. -/
theorem compactificationPullback_ι (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y')
    (g' : X' ⟶ X) (h_cart : IsPullback g' f' f g) (P : Of Y (Over.mk f)) :
    Of.ι (compactificationPullback f g f' g' h_cart P) =
      interiorLift f g f' g' h_cart P :=
  rfl

/-- The structure map of the base-changed compactification is `f̄'`. -/
theorem compactificationPullback_hom (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y')
    (g' : X' ⟶ X) (h_cart : IsPullback g' f' f g) (P : Of Y (Over.mk f)) :
    (compactificationPullback f g f' g' h_cart P).obj.right.hom =
      ambientToBase f g f' g' h_cart P :=
  rfl

/-- Interior, ambient, and cartesian identifications of the base-changed
compactification. -/
theorem compactificationPullback_spec (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y')
    (g' : X' ⟶ X) (h_cart : IsPullback g' f' f g) (P : Of Y (Over.mk f)) :
    Of.ι (compactificationPullback f g f' g' h_cart P) =
        interiorLift f g f' g' h_cart P ∧
      (compactificationPullback f g f' g' h_cart P).obj.right.hom =
        ambientToBase f g f' g' h_cart P ∧
      IsPullback (ambientToSource f g f' g' h_cart P)
          (ambientToBase f g f' g' h_cart P) P.obj.right.hom g ∧
      IsPullback g' (interiorLift f g f' g' h_cart P) (Of.ι P)
        (ambientToSource f g f' g' h_cart P) :=
  sorry

/-- The commutativity witness for the induced map of pulled-back ambients. -/
theorem ambientMapLift_fac (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y')
    (g' : X' ⟶ X) (h_cart : IsPullback g' f' f g) {P Q : Of Y (Over.mk f)}
    (φ : P ⟶ Q) :
    ambientToBase f g f' g' h_cart P ≫ g =
      (ambientToSource f g f' g' h_cart P ≫ Of.ambientMap φ) ≫
        Q.obj.right.hom :=
  ((pullback.condition :
        ambientToBase f g f' g' h_cart P ≫ g =
          ambientToSource f g f' g' h_cart P ≫ P.obj.right.hom).trans
    ((congrArg (fun h ↦ ambientToSource f g f' g' h_cart P ≫ h)
        (Of.ambientMap_comp_structure φ).symm).trans
      (Category.assoc (ambientToSource f g f' g' h_cart P) (Of.ambientMap φ)
        Q.obj.right.hom).symm))

/-- The scheme map of ambients `X̄'_P ⟶ X̄'_Q` induced by a morphism of
compactifications. -/
def ambientMapLift (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X)
    (h_cart : IsPullback g' f' f g) {P Q : Of Y (Over.mk f)} (φ : P ⟶ Q) :
    ambient f g f' g' h_cart P ⟶ ambient f g f' g' h_cart Q :=
  pullback.lift (ambientToBase f g f' g' h_cart P)
    (ambientToSource f g f' g' h_cart P ≫ Of.ambientMap φ)
    (ambientMapLift_fac f g f' g' h_cart φ)

/-- The induced ambient map lies over `Y'`. -/
theorem ambientMapLift_comp_toBase (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y')
    (g' : X' ⟶ X) (h_cart : IsPullback g' f' f g) {P Q : Of Y (Over.mk f)}
    (φ : P ⟶ Q) :
    ambientMapLift f g f' g' h_cart φ ≫ ambientToBase f g f' g' h_cart Q =
      ambientToBase f g f' g' h_cart P :=
  pullback.lift_fst (ambientToBase f g f' g' h_cart P)
    (ambientToSource f g f' g' h_cart P ≫ Of.ambientMap φ)
    (ambientMapLift_fac f g f' g' h_cart φ)

/-- The induced ambient map lies over the original ambient map of `φ`. -/
theorem ambientMapLift_comp_toSource (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y')
    (g' : X' ⟶ X) (h_cart : IsPullback g' f' f g) {P Q : Of Y (Over.mk f)}
    (φ : P ⟶ Q) :
    ambientMapLift f g f' g' h_cart φ ≫ ambientToSource f g f' g' h_cart Q =
      ambientToSource f g f' g' h_cart P ≫ Of.ambientMap φ :=
  pullback.lift_snd (ambientToBase f g f' g' h_cart P)
    (ambientToSource f g f' g' h_cart P ≫ Of.ambientMap φ)
    (ambientMapLift_fac f g f' g' h_cart φ)

/-- The induced interiors commute with `ambientMapLift`. -/
theorem interiorLift_comp_ambientMapLift (f : X ⟶ Y) (g : Y' ⟶ Y)
    (f' : X' ⟶ Y') (g' : X' ⟶ X) (h_cart : IsPullback g' f' f g)
    {P Q : Of Y (Over.mk f)} (φ : P ⟶ Q) :
    interiorLift f g f' g' h_cart P ≫ ambientMapLift f g f' g' h_cart φ =
      interiorLift f g f' g' h_cart Q :=
  sorry

/-- The ambient scheme of the constructed compactification is the fibre
product `ambient`. -/
theorem compactificationPullback_obj_right_left (f : X ⟶ Y) (g : Y' ⟶ Y)
    (f' : X' ⟶ Y') (g' : X' ⟶ X) (h_cart : IsPullback g' f' f g)
    (P : Of Y (Over.mk f)) :
    (compactificationPullback f g f' g' h_cart P).obj.right.left =
      ambient f g f' g' h_cart P :=
  rfl


variable {Y Z : Scheme.{u}} (X : Over Y) (g : Y ⟶ Z)
variable {X' Y' Z' : Scheme.{u}}

/-- Compactification of `g'` obtained by base change of `C.P_g`. -/
def CompDiagram.pullback_P_g [IsSeparated g] [Scheme.Hom.FiniteType g]
    (C : CompDiagram X g) (f' : X' ⟶ Y') (g' : Y' ⟶ Z') (a : Z' ⟶ Z)
    (b : Y' ⟶ Y) (c : X' ⟶ X.left) (_h_upper : IsPullback c f' X.hom b)
    (h_lower : IsPullback b g' g a) :
    Of Z' (Over.mk g') :=
  compactificationPullback g a g' b h_lower C.P_g

/-- The ambient square of the pulled-back `P_bar` is cartesian. -/
theorem CompDiagram.pullback_P_bar_isPullback
    [IsSeparated X.hom] [Scheme.Hom.FiniteType X.hom]
    [IsSeparated g] [Scheme.Hom.FiniteType g]
    [CompactSpace X.left] [QuasiSeparatedSpace X.left]
    [CompactSpace Y] [QuasiSeparatedSpace Y]
    [CompactSpace Z] [QuasiSeparatedSpace Z]
    (C : CompDiagram X g) (f' : X' ⟶ Y') (g' : Y' ⟶ Z') (a : Z' ⟶ Z)
    (b : Y' ⟶ Y) (c : X' ⟶ X.left) (h_upper : IsPullback c f' X.hom b)
    (h_lower : IsPullback b g' g a) :
    IsPullback c
      (f' ≫ Of.ι (CompDiagram.pullback_P_g X g C f' g' a b c h_upper h_lower))
      (X.hom ≫ Of.ι C.P_g)
      (ambientToSource g a g' b h_lower C.P_g) :=
  sorry

/-- Compactification diagram of `f'` and `g'` obtained by base change of `C`. -/
def CompDiagram.pullback
    [IsSeparated X.hom] [Scheme.Hom.FiniteType X.hom]
    [IsSeparated g] [Scheme.Hom.FiniteType g]
    [CompactSpace X.left] [QuasiSeparatedSpace X.left]
    [CompactSpace Y] [QuasiSeparatedSpace Y]
    [CompactSpace Z] [QuasiSeparatedSpace Z]
    (C : CompDiagram X g) (f' : X' ⟶ Y') (g' : Y' ⟶ Z') (a : Z' ⟶ Z)
    (b : Y' ⟶ Y) (c : X' ⟶ X.left) (h_upper : IsPullback c f' X.hom b)
    (h_lower : IsPullback b g' g a)
    [IsSeparated f'] [Scheme.Hom.FiniteType f']
    [IsSeparated g'] [Scheme.Hom.FiniteType g']
    [CompactSpace X'] [QuasiSeparatedSpace X']
    [CompactSpace Y'] [QuasiSeparatedSpace Y']
    [CompactSpace Z'] [QuasiSeparatedSpace Z'] :
    CompDiagram (Over.mk f') g' :=
  let P_g' := CompDiagram.pullback_P_g X g C f' g' a b c h_upper h_lower
  CompDiagram.of (Over.mk f') g' P_g'
    (compactificationPullback (X.hom ≫ Of.ι C.P_g)
      (ambientToSource g a g' b h_lower C.P_g)
      (f' ≫ Of.ι P_g') c
      (CompDiagram.pullback_P_bar_isPullback X g C f' g' a b c h_upper h_lower)
      C.P_bar)

end etaleDerivedLowerShriek
end AlgebraicGeometry.Scheme.Etale

end
