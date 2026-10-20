module

public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.CommSq

/-!
# Objectwise adjunction base-change maps

Mathlib owns the general mates equivalence for a square of left adjoints.
This leaf gives its right mate at a single object together with the
adjunction-transpose predicate used by applications that construct or compare
one component at a time.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe uDX uDX' uDY uDY' vDX vDX' vDY vDY'

namespace CategoryTheory

section

variable {DX : Type uDX} {DX' : Type uDX'} {DY : Type uDY} {DY' : Type uDY'}
variable [Category.{vDX} DX] [Category.{vDX'} DX'] [Category.{vDY} DY] [Category.{vDY'} DY']

variable
  (Lf : DY ⥤ DX)
  (Lf' : DY' ⥤ DX')
  (Lg : DY ⥤ DY')
  (Lg' : DX ⥤ DX')
  (Rf : DX ⥤ DY)
  (Rf' : DX' ⥤ DY')
  (adj_f : Lf ⊣ Rf)
  (adj_f' : Lf' ⊣ Rf')
  (squareIso : Lg ⋙ Lf' ≅ Lf ⋙ Lg')

/-- A morphism is the objectwise right mate of a square of left adjoints exactly when its
transpose is the square comparison followed by the first adjunction counit. -/
def IsDerivedBaseChangeMap
    (K : DX)
    (η : Lg.obj (Rf.obj K) ⟶ Rf'.obj (Lg'.obj K)) : Prop :=
  ((adj_f'.homEquiv (Lg.obj (Rf.obj K)) (Lg'.obj K)).symm η) =
    (squareIso.hom.app (Rf.obj K) ≫ Lg'.map (adj_f.counit.app K))

/-- The objectwise right mate of `squareIso`, expressed using Mathlib's `mateEquiv`.

The historical name is retained because derived-category applications conventionally call this
component their derived base-change map. -/
noncomputable def derivedBaseChangeMap
    (K : DX) :
    Lg.obj (Rf.obj K) ⟶ Rf'.obj (Lg'.obj K) :=
  (mateEquiv adj_f adj_f' squareIso.hom).app K

/-- Transposing `derivedBaseChangeMap` across `adj_f'` recovers the counit formula prescribed by
the original square. -/
theorem derivedBaseChangeMap_spec
    (K : DX) :
    ((adj_f'.homEquiv (Lg.obj (Rf.obj K)) (Lg'.obj K)).symm
        (derivedBaseChangeMap Lf Lf' Lg Lg' Rf Rf' adj_f adj_f' squareIso K)) =
      (squareIso.hom.app (Rf.obj K) ≫ Lg'.map (adj_f.counit.app K)) := sorry

/-- Any objectwise map satisfying the adjunction-transpose base-change formula agrees with the
canonical right mate. -/
theorem IsDerivedBaseChangeMap.eq_derivedBaseChangeMap
    {K : DX}
    {η : Lg.obj (Rf.obj K) ⟶ Rf'.obj (Lg'.obj K)}
    (hη : IsDerivedBaseChangeMap Lf Lf' Lg Lg' Rf Rf' adj_f adj_f' squareIso K η) :
    η = derivedBaseChangeMap Lf Lf' Lg Lg' Rf Rf' adj_f adj_f' squareIso K := sorry

namespace DerivedBaseChange

/- The right-square form is the interface needed by lower-shriek/forgetful comparisons.  It keeps
the square itself explicit, so a caller can choose the canonical derived model appropriate to its
site or geometric presentation. -/

/-- The mate of an explicit square of right adjoints.

Given `Lf ⊣ Rf` and `Lf' ⊣ Rf'`, a square
`Rf ⋙ G ⟶ H ⋙ Rf'` determines a natural transformation
`G ⋙ Lf' ⟶ Lf ⋙ H`.  The square is deliberately an argument rather than an ambient instance:
in derived applications it records the chosen comparison between forgetful functors. -/
@[stacks 02N8 "right-adjoint square mate"]
noncomputable def mapOfRight
    {Lf : DY ⥤ DX} {Lf' : DY' ⥤ DX'}
    {Rf : DX ⥤ DY} {Rf' : DX' ⥤ DY'}
    {G : DY ⥤ DY'} {H : DX ⥤ DX'}
    (adj_f : Lf ⊣ Rf) (adj_f' : Lf' ⊣ Rf')
    (square : TwoSquare Rf H G Rf') :
    G ⋙ Lf' ⟶ Lf ⋙ H :=
  ((mateEquiv adj_f adj_f').symm square).natTrans

/-- Taking the mate of the right-square construction recovers the original square. -/
@[stacks 02N8 "right-adjoint square mate specification"]
theorem mapOfRight_mate
    {Lf : DY ⥤ DX} {Lf' : DY' ⥤ DX'}
    {Rf : DX ⥤ DY} {Rf' : DX' ⥤ DY'}
    {G : DY ⥤ DY'} {H : DX ⥤ DX'}
    (adj_f : Lf ⊣ Rf) (adj_f' : Lf' ⊣ Rf')
    (square : TwoSquare Rf H G Rf') :
    mateEquiv adj_f adj_f'
      (TwoSquare.mk G Lf Lf' H (mapOfRight adj_f adj_f' square)) =
        square := sorry

/-- The fully explicit implementation of the natural transformation obtained by taking the right
mate of a square of left adjoints. -/
@[stacks 02N8 "unbounded derived base-change mate"]
noncomputable def mapExplicit :
    Rf ⋙ Lg ⟶ Lg' ⋙ Rf' :=
  (mateEquiv adj_f adj_f' squareIso.hom).natTrans

/-- The natural transformation obtained by taking the right mate of a square of left adjoints.
The adjunctions and the square determine all six functors, so they remain implicit here. -/
@[stacks 02N8 "unbounded derived base-change mate"]
noncomputable def map
    {Lf : DY ⥤ DX} {Lf' : DY' ⥤ DX'}
    {Lg : DY ⥤ DY'} {Lg' : DX ⥤ DX'}
    {Rf : DX ⥤ DY} {Rf' : DX' ⥤ DY'}
    (adj_f : Lf ⊣ Rf) (adj_f' : Lf' ⊣ Rf')
    (squareIso : Lg ⋙ Lf' ≅ Lf ⋙ Lg') :
    Rf ⋙ Lg ⟶ Lg' ⋙ Rf' :=
  mapExplicit Lf Lf' Lg Lg' Rf Rf' adj_f adj_f' squareIso

/-- The component of the canonical derived base-change transformation at `K`. -/
@[stacks 02N8 "unbounded derived base-change component"]
noncomputable abbrev app
    {Lf : DY ⥤ DX} {Lf' : DY' ⥤ DX'}
    {Lg : DY ⥤ DY'} {Lg' : DX ⥤ DX'}
    {Rf : DX ⥤ DY} {Rf' : DX' ⥤ DY'}
    (adj_f : Lf ⊣ Rf) (adj_f' : Lf' ⊣ Rf')
    (squareIso : Lg ⋙ Lf' ≅ Lf ⋙ Lg') (K : DX) :
    Lg.obj (Rf.obj K) ⟶ Rf'.obj (Lg'.obj K) :=
  (map adj_f adj_f' squareIso).app K

/-- The objectwise predicate for a component of the canonical derived base-change map. -/
@[stacks 02N8 "unbounded derived base-change component specification"]
abbrev IsMapAt
    {Lf : DY ⥤ DX} {Lf' : DY' ⥤ DX'}
    {Lg : DY ⥤ DY'} {Lg' : DX ⥤ DX'}
    {Rf : DX ⥤ DY} {Rf' : DX' ⥤ DY'}
    (adj_f : Lf ⊣ Rf) (adj_f' : Lf' ⊣ Rf')
    (squareIso : Lg ⋙ Lf' ≅ Lf ⋙ Lg') (K : DX)
    (η : Lg.obj (Rf.obj K) ⟶ Rf'.obj (Lg'.obj K)) : Prop :=
  IsDerivedBaseChangeMap Lf Lf' Lg Lg' Rf Rf' adj_f adj_f' squareIso K η

/-- The canonical component satisfies the derived base-change mate equation. -/
@[stacks 02N8 "unbounded derived base-change component specification"]
theorem map_isMapAt
    {Lf : DY ⥤ DX} {Lf' : DY' ⥤ DX'}
    {Lg : DY ⥤ DY'} {Lg' : DX ⥤ DX'}
    {Rf : DX ⥤ DY} {Rf' : DX' ⥤ DY'}
    (adj_f : Lf ⊣ Rf) (adj_f' : Lf' ⊣ Rf')
    (squareIso : Lg ⋙ Lf' ≅ Lf ⋙ Lg') (K : DX) :
    IsMapAt adj_f adj_f' squareIso K (app adj_f adj_f' squareIso K) := sorry

/-- The component of `map` is characterized by the adjunction-transpose formula.

This is the objectwise specification users can transport across concrete realizations of the
functors; it avoids exposing the implementation through `mateEquiv`. -/
@[stacks 02N8 "unbounded derived base-change component specification"]
theorem map_spec
    {Lf : DY ⥤ DX} {Lf' : DY' ⥤ DX'}
    {Lg : DY ⥤ DY'} {Lg' : DX ⥤ DX'}
    {Rf : DX ⥤ DY} {Rf' : DX' ⥤ DY'}
    (adj_f : Lf ⊣ Rf) (adj_f' : Lf' ⊣ Rf')
    (squareIso : Lg ⋙ Lf' ≅ Lf ⋙ Lg') (K : DX) :
    ((adj_f'.homEquiv (Lg.obj (Rf.obj K)) (Lg'.obj K)).symm
        (app adj_f adj_f' squareIso K)) =
      (squareIso.hom.app (Rf.obj K) ≫ Lg'.map (adj_f.counit.app K)) := sorry

/-- The right mate of a square of left adjoints commutes with the two adjunction counits. -/
@[stacks 02N8 "unbounded derived base-change counit square"]
theorem counitCommSq
    {Lf : DY ⥤ DX} {Lf' : DY' ⥤ DX'}
    {Lg : DY ⥤ DY'} {Lg' : DX ⥤ DX'}
    {Rf : DX ⥤ DY} {Rf' : DX' ⥤ DY'}
    (adj_f : Lf ⊣ Rf) (adj_f' : Lf' ⊣ Rf')
    (squareIso : Lg ⋙ Lf' ≅ Lf ⋙ Lg') (K : DX) :
    CommSq
      (squareIso.inv.app (Rf.obj K) ≫
        Lf'.map (app adj_f adj_f' squareIso K))
      (Lg'.map (adj_f.counit.app K))
      (adj_f'.counit.app (Lg'.obj K))
      (𝟙 (Lg'.obj K)) := sorry

/-- Composing a derived base-change component with the target counit recovers the image of the
source counit. -/
@[stacks 02N8 "unbounded derived base-change counit compatibility"]
theorem app_comp_counit
    {Lf : DY ⥤ DX} {Lf' : DY' ⥤ DX'}
    {Lg : DY ⥤ DY'} {Lg' : DX ⥤ DX'}
    {Rf : DX ⥤ DY} {Rf' : DX' ⥤ DY'}
    (adj_f : Lf ⊣ Rf) (adj_f' : Lf' ⊣ Rf')
    (squareIso : Lg ⋙ Lf' ≅ Lf ⋙ Lg') (K : DX) :
    squareIso.inv.app (Rf.obj K) ≫
        Lf'.map (app adj_f adj_f' squareIso K) ≫
          adj_f'.counit.app (Lg'.obj K) =
      Lg'.map (adj_f.counit.app K) := sorry

/-- The unit of the first adjunction, followed by the derived base-change mate and the
inverse square isomorphism, is the unit of the second adjunction. -/
theorem unit_comp_app
    {Lf : DY ⥤ DX} {Lf' : DY' ⥤ DX'}
    {Lg : DY ⥤ DY'} {Lg' : DX ⥤ DX'}
    {Rf : DX ⥤ DY} {Rf' : DX' ⥤ DY'}
    (adj_f : Lf ⊣ Rf) (adj_f' : Lf' ⊣ Rf')
    (squareIso : Lg ⋙ Lf' ≅ Lf ⋙ Lg') (c : DY) :
    Lg.map (adj_f.unit.app c) ≫
        app adj_f adj_f' squareIso (Lf.obj c) ≫
      Rf'.map (squareIso.inv.app c) =
    adj_f'.unit.app (Lg.obj c) := sorry

/-- A component satisfying the mate equation is the canonical component. -/
@[stacks 02N8 "uniqueness of unbounded derived base-change components"]
theorem IsMapAt.eq_app
    {Lf : DY ⥤ DX} {Lf' : DY' ⥤ DX'}
    {Lg : DY ⥤ DY'} {Lg' : DX ⥤ DX'}
    {Rf : DX ⥤ DY} {Rf' : DX' ⥤ DY'}
    (adj_f : Lf ⊣ Rf) (adj_f' : Lf' ⊣ Rf')
    (squareIso : Lg ⋙ Lf' ≅ Lf ⋙ Lg')
    {K : DX} {η : Lg.obj (Rf.obj K) ⟶ Rf'.obj (Lg'.obj K)}
    (hη : IsMapAt adj_f adj_f' squareIso K η) :
    η = app adj_f adj_f' squareIso K := sorry

/-- The natural-transformation form of the derived base-change specification. -/
@[stacks 02N8 "unbounded derived base-change specification"]
def IsMap
    {Lf : DY ⥤ DX} {Lf' : DY' ⥤ DX'}
    {Lg : DY ⥤ DY'} {Lg' : DX ⥤ DX'}
    {Rf : DX ⥤ DY} {Rf' : DX' ⥤ DY'}
    (adj_f : Lf ⊣ Rf) (adj_f' : Lf' ⊣ Rf')
    (squareIso : Lg ⋙ Lf' ≅ Lf ⋙ Lg')
    (η : Rf ⋙ Lg ⟶ Lg' ⋙ Rf') : Prop :=
  ∀ K, IsMapAt adj_f adj_f' squareIso K (η.app K)

/-- The canonical derived base-change transformation satisfies its specification. -/
@[stacks 02N8 "unbounded derived base-change specification"]
theorem map_isMap
    {Lf : DY ⥤ DX} {Lf' : DY' ⥤ DX'}
    {Lg : DY ⥤ DY'} {Lg' : DX ⥤ DX'}
    {Rf : DX ⥤ DY} {Rf' : DX' ⥤ DY'}
    (adj_f : Lf ⊣ Rf) (adj_f' : Lf' ⊣ Rf')
    (squareIso : Lg ⋙ Lf' ≅ Lf ⋙ Lg') :
    IsMap adj_f adj_f' squareIso (map adj_f adj_f' squareIso) := sorry

/-- A natural transformation satisfying the mate equation is the canonical map. -/
@[stacks 02N8 "uniqueness of unbounded derived base-change maps"]
theorem IsMap.eq_map
    {Lf : DY ⥤ DX} {Lf' : DY' ⥤ DX'}
    {Lg : DY ⥤ DY'} {Lg' : DX ⥤ DX'}
    {Rf : DX ⥤ DY} {Rf' : DX' ⥤ DY'}
    (adj_f : Lf ⊣ Rf) (adj_f' : Lf' ⊣ Rf')
    (squareIso : Lg ⋙ Lf' ≅ Lf ⋙ Lg')
    {η : Rf ⋙ Lg ⟶ Lg' ⋙ Rf'}
    (hη : IsMap adj_f adj_f' squareIso η) :
    η = map adj_f adj_f' squareIso := sorry

end DerivedBaseChange

end

end CategoryTheory
