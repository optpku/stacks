module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Flat.EtaleNeighborhood
public import ReasLib.AlgebraicGeometry.Scheme.Module.Flat.EtaleProjective
public import ReasLib.AlgebraicGeometry.Scheme.Etale.Neighborhood.Cofiltered
public import ReasLib.Algebra.Module.Projective.LocalRing
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FinitePresentation

/-!
# Free global sections after an étale refinement

This module records pointwise and fibrewise étale-local freeness of the global sections
of a finite-type quasicoherent module.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- A finite-type quasicoherent module flat at a point over a locally finitely presented
morphism becomes finitely presented with free global sections after an elementary étale
refinement of the base and an affine étale refinement of the source. -/
@[stacks 05KY]
theorem existsEtaleRefinementWithFreeSections {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFinitePresentation f] (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType]
    (x : X) (h_flat : flatOverAt F f x) :
    ∃ U : EtaleNeighborhood.Elementary S (f x),
      let E := U.obj
      let T := E.toEtale.left
      let R := T.presheaf.stalk E.point
      let b := T.fromSpecStalk E.point ≫ E.toEtale.hom
      let P := Limits.pullback f b
      ∃ Y : P.Etale,
        let X' := Y.left
        let g := Y.hom ≫ Limits.pullback.fst f b
        let p := Y.hom ≫ Limits.pullback.snd f b
        let x₀ := IsLocalRing.closedPoint R
        let F' := (Scheme.Modules.pullback g).obj F
        ∃ x' : X',
          ∃ (_ : g x' = x) (_ : p x' = x₀) (_ : IsIso (g.residueFieldMap x'))
            (_ : IsAffine X') (_ : Scheme.Hom.FinitePresentation p)
            (_ : F'.IsFinitePresentation),
            Module.Free R (Scheme.Hom.globalSectionsMod p F' : ModuleCat R) := sorry

/-- A finite-type quasicoherent module flat at a point over a locally finite-type morphism
has free global sections after an elementary étale refinement of the base and an affine
étale refinement of the source that preserves the residue field at the point. -/
@[stacks 05KZ]
theorem existsEtaleRefinementWithFreeSections_of_locallyOfFiniteType
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType]
    (x : X) (h_flat : flatOverAt F f x) :
    ∃ U : EtaleNeighborhood.Elementary S (f x),
      let E := U.obj
      let T := E.toEtale.left
      let R := T.presheaf.stalk E.point
      let b := T.fromSpecStalk E.point ≫ E.toEtale.hom
      let P := Limits.pullback f b
      ∃ Y : P.Etale,
        let X' := Y.left
        let g := Y.hom ≫ Limits.pullback.fst f b
        let p := Y.hom ≫ Limits.pullback.snd f b
        let x₀ := IsLocalRing.closedPoint R
        let F' := (Scheme.Modules.pullback g).obj F
        ∃ x' : X',
          ∃ (_ : g x' = x) (_ : p x' = x₀) (_ : IsIso (g.residueFieldMap x'))
            (_ : IsAffine X'),
            Module.Free R (Scheme.Hom.globalSectionsMod p F' : ModuleCat R) := sorry

/-- A finite-type quasicoherent module that is flat over the base along a fibre of a
finitely presented morphism admits, after an elementary étale base neighborhood, an
affine étale refinement covering that fibre, with finitely presented pullback and free
global sections. -/
@[stacks 05L0]
theorem existsEtaleCoverWithFreeSections {X S : Scheme.{u}} (f : X ⟶ S)
    [Scheme.Hom.FinitePresentation f] (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType]
    (s : S) (h_flat : ∀ x : f.fiber s, flatOverAt F f (f.fiberι s x)) :
    ∃ U : EtaleNeighborhood.Elementary S s,
      let E := U.obj
      let T := E.toEtale.left
      let R := T.presheaf.stalk E.point
      let b := T.fromSpecStalk E.point ≫ E.toEtale.hom
      let P := Limits.pullback f b
      ∃ Y : P.Etale,
        let X' := Y.left
        let g := Y.hom ≫ Limits.pullback.fst f b
        let p := Y.hom ≫ Limits.pullback.snd f b
        let x₀ := IsLocalRing.closedPoint R
        let F' := (Scheme.Modules.pullback g).obj F
        ∃ (_ : Set.range (f.fiberι s) = Set.range (p.fiberι x₀ ≫ g))
          (_ : IsAffine X') (_ : Scheme.Hom.FinitePresentation p)
          (_ : F'.IsFinitePresentation),
          Module.Free R (Scheme.Hom.globalSectionsMod p F' : ModuleCat R) := sorry

/-- A finite-type quasicoherent module that is flat over the base along a fibre of a
finite-type morphism admits, after an elementary étale base neighborhood, an affine
étale refinement covering that fibre and having free global sections. -/
@[stacks 05L1]
theorem existsEtaleCoverWithFreeSections_of_finiteType {X S : Scheme.{u}} (f : X ⟶ S)
    [Scheme.Hom.FiniteType f] (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType]
    (s : S) (h_flat : ∀ x : f.fiber s, flatOverAt F f (f.fiberι s x)) :
    ∃ U : EtaleNeighborhood.Elementary S s,
      let E := U.obj
      let T := E.toEtale.left
      let R := T.presheaf.stalk E.point
      let b := T.fromSpecStalk E.point ≫ E.toEtale.hom
      let P := Limits.pullback f b
      ∃ Y : P.Etale,
        let X' := Y.left
        let g := Y.hom ≫ Limits.pullback.fst f b
        let p := Y.hom ≫ Limits.pullback.snd f b
        let x₀ := IsLocalRing.closedPoint R
        let F' := (Scheme.Modules.pullback g).obj F
        ∃ (_ : Set.range (f.fiberι s) = Set.range (p.fiberι x₀ ≫ g)) (_ : IsAffine X'),
          Module.Free R (Scheme.Hom.globalSectionsMod p F' : ModuleCat R) := sorry

end AlgebraicGeometry.Scheme.Modules
