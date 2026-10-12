/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Fiber.Stalk

/-!
# Base change of scheme-theoretic fibres

This leaf names the morphism between fixed scheme-theoretic fibres induced by
a pullback square and records its basic compatibility properties.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- The morphism between scheme-theoretic fibres induced by a commutative
square and a point of its upper-right scheme. -/
noncomputable def fiberMap {X' S' X S : Scheme.{u}}
    (f' : X' ⟶ S') (i : X' ⟶ X) (g : S' ⟶ S) (f : X ⟶ S)
    (sq : CommSq i f' f g) (s' : S') :
    f'.fiber s' ⟶ f.fiber (g s') :=
  pullback.map f' (S'.fromSpecResidueField s') f
    (S.fromSpecResidueField (g s')) i (Spec.map (g.residueFieldMap s')) g sq.w.symm
    (g.SpecMap_residueFieldMap_fromSpecResidueField s').symm

/-- The morphism between fibres induced by a commutative square is compatible
with the projections to the source schemes. -/
@[reassoc]
theorem fiberMap_fiberι {X' S' X S : Scheme.{u}}
    (f' : X' ⟶ S') (i : X' ⟶ X) (g : S' ⟶ S) (f : X ⟶ S)
    (sq : CommSq i f' f g) (s' : S') :
    fiberMap f' i g f sq s' ≫ f.fiberι (g s') = f'.fiberι s' ≫ i := sorry

/-- The morphism between fibres induced by a commutative square is compatible
with the projections to the spectra of the base residue fields. -/
@[reassoc]
theorem fiberMap_fiberToSpecResidueField {X' S' X S : Scheme.{u}}
    (f' : X' ⟶ S') (i : X' ⟶ X) (g : S' ⟶ S) (f : X ⟶ S)
    (sq : CommSq i f' f g) (s' : S') :
    fiberMap f' i g f sq s' ≫ f.fiberToSpecResidueField (g s') =
      f'.fiberToSpecResidueField s' ≫ Spec.map (g.residueFieldMap s') := sorry

/-- The morphism `X'_{s'} ⟶ X_{g(s')}` between fixed scheme-theoretic fibres
induced by a pullback square. -/
noncomputable def baseChangeFiberMap {S X S' X' : Scheme.{u}}
    (f : X ⟶ S) (g : S' ⟶ S) (g' : X' ⟶ X) (f' : X' ⟶ S')
    (hpb : IsPullback g' f' f g) (s' : S') :
    f'.fiber s' ⟶ f.fiber (g s') :=
  fiberMap f' g' g f hpb.toCommSq s'

/-- The local ring at the distinguished point of the fibre of the induced
map `X'_{f'(x')} ⟶ X_{g(f'(x'))}`. -/
noncomputable abbrev baseChangeFiberStalkAt {S X S' X' : Scheme.{u}}
    (f : X ⟶ S) (g : S' ⟶ S) (g' : X' ⟶ X) (f' : X' ⟶ S')
    (hpb : IsPullback g' f' f g) (x' : X') : CommRingCat :=
  fiberStalkAt (baseChangeFiberMap f g g' f' hpb (f' x')) (f'.asFiber x')

/-- The induced map between fixed fibres is compatible with their morphisms
to the source schemes. -/
@[reassoc]
theorem baseChangeFiberMap_fiberι {S X S' X' : Scheme.{u}}
    (f : X ⟶ S) (g : S' ⟶ S) (g' : X' ⟶ X) (f' : X' ⟶ S')
    (hpb : IsPullback g' f' f g) (s' : S') :
    baseChangeFiberMap f g g' f' hpb s' ≫ f.fiberι (g s') =
      f'.fiberι s' ≫ g' := sorry

/-- The induced map between fixed fibres is compatible with the projections
to the spectra of the base residue fields. -/
@[reassoc]
theorem baseChangeFiberMap_fiberToSpecResidueField {S X S' X' : Scheme.{u}}
    (f : X ⟶ S) (g : S' ⟶ S) (g' : X' ⟶ X) (f' : X' ⟶ S')
    (hpb : IsPullback g' f' f g) (s' : S') :
    baseChangeFiberMap f g g' f' hpb s' ≫ f.fiberToSpecResidueField (g s') =
      f'.fiberToSpecResidueField s' ≫ Spec.map (g.residueFieldMap s') := sorry

/-- The square formed by the induced map between fixed fibres and the
residue-field projections is a pullback square. -/
theorem isPullback_baseChangeFiberMap {S X S' X' : Scheme.{u}}
    (f : X ⟶ S) (g : S' ⟶ S) (g' : X' ⟶ X) (f' : X' ⟶ S')
    (hpb : IsPullback g' f' f g) (s' : S') :
    IsPullback (baseChangeFiberMap f g g' f' hpb s')
      (f'.fiberToSpecResidueField s') (f.fiberToSpecResidueField (g s'))
      (Spec.map (g.residueFieldMap s')) := sorry

end AlgebraicGeometry.Scheme.Hom
