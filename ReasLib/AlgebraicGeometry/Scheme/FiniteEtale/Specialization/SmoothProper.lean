/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.FiniteEtale.Specialization.Surjective
public import ReasLib.Topology.Category.ProfiniteGrp.PrimeToP
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.PreGaloisCategory
open AlgebraicGeometry

universe u w

namespace EtaleFundamentalGroup.IsSpecializationMap

/-- For a smooth proper morphism with geometrically connected fibers, a specialization
map to a fiber whose residue field has characteristic zero is bijective. -/
theorem bijective {X S : Scheme.{u}} (f : X ⟶ S)
    [Smooth f] [IsProper f] [GeometricallyConnected f]
    (sbar' sbar : Scheme.GeometricPoint S)
    (hSpec : Specializes sbar'.image sbar.image)
    (hchar : ringChar (S.residueField sbar.image) = 0)
    (F' : Scheme.FiniteEtale (pullback f sbar'.hom) ⥤ FintypeCat.{w})
    (F : Scheme.FiniteEtale (pullback f sbar.hom) ⥤ FintypeCat.{w})
    [GaloisCategory (Scheme.FiniteEtale (pullback f sbar'.hom))]
    [FiberFunctor F']
    [GaloisCategory (Scheme.FiniteEtale (pullback f sbar.hom))]
    [FiberFunctor F]
    (sp : ContinuousMonoidHom (Aut F') (Aut F))
    (hsp : EtaleFundamentalGroup.IsSpecializationMap f sbar' sbar hSpec F' F sp) :
    Function.Bijective sp := sorry

/-- For a smooth proper morphism with geometrically connected fibers, a specialization
map to a fiber whose residue field has prime characteristic `p` is surjective. -/
theorem surjective_of_smooth_char {X S : Scheme.{u}} (f : X ⟶ S)
    [Smooth f] [IsProper f] [GeometricallyConnected f]
    (sbar' sbar : Scheme.GeometricPoint S)
    (hSpec : Specializes sbar'.image sbar.image)
    (p : ℕ) (hp : Nat.Prime p)
    (hchar : ringChar (S.residueField sbar.image) = p)
    (F' : Scheme.FiniteEtale (pullback f sbar'.hom) ⥤ FintypeCat.{w})
    (F : Scheme.FiniteEtale (pullback f sbar.hom) ⥤ FintypeCat.{w})
    [GaloisCategory (Scheme.FiniteEtale (pullback f sbar'.hom))]
    [FiberFunctor F']
    [GaloisCategory (Scheme.FiniteEtale (pullback f sbar.hom))]
    [FiberFunctor F]
    (sp : ContinuousMonoidHom (Aut F') (Aut F))
    (hsp : EtaleFundamentalGroup.IsSpecializationMap f sbar' sbar hSpec F' F sp) :
    Function.Surjective sp := sorry

/-- For a smooth proper morphism with geometrically connected fibers, a specialization
map to a fiber whose residue field has prime characteristic `p` induces a bijection
on maximal prime-to-`p` quotients. -/
theorem primeToPQuotientMap_bijective {X S : Scheme.{u}} (f : X ⟶ S)
    [Smooth f] [IsProper f] [GeometricallyConnected f]
    (sbar' sbar : Scheme.GeometricPoint S)
    (hSpec : Specializes sbar'.image sbar.image)
    (p : ℕ) (hp : Nat.Prime p)
    (hchar : ringChar (S.residueField sbar.image) = p)
    (F' : Scheme.FiniteEtale (pullback f sbar'.hom) ⥤ FintypeCat.{w})
    (F : Scheme.FiniteEtale (pullback f sbar.hom) ⥤ FintypeCat.{w})
    [GaloisCategory (Scheme.FiniteEtale (pullback f sbar'.hom))]
    [FiberFunctor F']
    [GaloisCategory (Scheme.FiniteEtale (pullback f sbar.hom))]
    [FiberFunctor F]
    (sp : ContinuousMonoidHom (Aut F') (Aut F))
    (hsp : EtaleFundamentalGroup.IsSpecializationMap f sbar' sbar hSpec F' F sp) :
    Function.Bijective
      (ProfiniteGrp.primeToPQuotientMap p (ProfiniteGrp.ofHom sp)) := sorry

end EtaleFundamentalGroup.IsSpecializationMap
