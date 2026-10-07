module

public import Mathlib.AlgebraicGeometry.Gluing
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization
public import Mathlib.RingTheory.GradedAlgebra.RingHom

/-!
# Maps of projective spectra: basic domain data

This leaf owns the open domain and glued local morphism associated to a graded ring map.
It deliberately does not assume a choice of twists on `Proj`; twist comparison data lives in
`ProjectiveSpectrum.Twist.Presentation` and `ProjectiveSpectrum.Map.Twist`.
-/

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits
open HomogeneousLocalization

noncomputable section

universe u

namespace AlgebraicGeometry

section

variable {A B sigma tau : Type u} [CommRing A] [SetLike sigma A] [AddSubgroupClass sigma A]
  [CommRing B] [SetLike tau B] [AddSubgroupClass tau B]
  {calA : Nat -> sigma} {calB : Nat -> tau} [GradedRing calA] [GradedRing calB]

/-- A homogeneous element together with an explicit strictly positive degree in the graded ring
`calA`. -/
structure PositiveHomogeneous (calA : Nat -> sigma) [GradedRing calA] where
  /-- The underlying ring element. -/
  val : A
  /-- A degree in which the element is homogeneous. -/
  degree : Nat
  /-- The stored degree is strictly positive. -/
  degree_pos : 0 < degree
  /-- The underlying element belongs to the stored homogeneous component. -/
  mem_degree : val ∈ calA degree

/-- The open domain on which a graded ring map induces a morphism of projective spectra. -/
abbrev projMapDomain (psi : calA →+*ᵍ calB) : (Proj calB).Opens :=
  iSup fun f : PositiveHomogeneous calA => Proj.basicOpen calB (psi f.1)

/-- A positive homogeneous basic open is contained in the domain of the induced `Proj` map. -/
theorem basicOpen_le_projMapDomain
    (psi : calA →+*ᵍ calB) {f : A} {d : Nat} (hd : 0 < d) (hf : f ∈ calA d) :
    Proj.basicOpen calB (psi f) <= projMapDomain psi := sorry

namespace PositiveHomogeneous

/-- Transport a positive homogeneous element through a graded ring homomorphism. -/
def map (psi : calA →+*ᵍ calB) (f : PositiveHomogeneous calA) :
    PositiveHomogeneous calB where
  val := psi f.1
  degree := f.degree
  degree_pos := f.degree_pos
  mem_degree := psi.2 f.mem_degree

end PositiveHomogeneous

/-- The standard-open cover of the domain of a graded `Proj` map. -/
abbrev projMapOpenCover
    (psi : calA →+*ᵍ calB) :
    (projMapDomain psi).toScheme.OpenCover :=
  Scheme.Opens.iSupOpenCover (fun f : PositiveHomogeneous calA => Proj.basicOpen calB (psi f.1))

/-- The affine-local morphism on a positive homogeneous basic open used to construct a `Proj`
map. -/
noncomputable abbrev projMapBasicOpenMap
    (psi : calA →+*ᵍ calB) (f : PositiveHomogeneous calA) :
    (projMapOpenCover psi).X f ⟶ Proj calA :=
  (Proj.basicOpenIsoSpec calB (psi f.1) (psi.2 (PositiveHomogeneous.mem_degree f))
      (PositiveHomogeneous.degree_pos f)).hom ≫
    Spec.map (CommRingCat.ofHom (Away.map psi f.1)) ≫
      Proj.awayι calA f.1 (PositiveHomogeneous.mem_degree f) (PositiveHomogeneous.degree_pos f)

/-- The affine-local maps defining a graded `Proj` map agree on pairwise overlaps. -/
theorem projMapBasicOpenMap_compatible
    (psi : calA →+*ᵍ calB) (f g : PositiveHomogeneous calA) :
    pullback.fst ((projMapOpenCover psi).f f) ((projMapOpenCover psi).f g) ≫
        projMapBasicOpenMap psi f =
      pullback.snd ((projMapOpenCover psi).f f) ((projMapOpenCover psi).f g) ≫
        projMapBasicOpenMap psi g := sorry

/-- The morphism from the natural open domain of a graded map to the source projective spectrum. -/
noncomputable def projMapMap
    (psi : calA →+*ᵍ calB) :
    (projMapDomain psi).toScheme ⟶ Proj calA :=
  (projMapOpenCover psi).glueMorphisms (projMapBasicOpenMap psi)
    (projMapBasicOpenMap_compatible psi)

/-- The inverse image of a positive homogeneous basic open under the canonical projective-spectrum
map is the corresponding basic open in the target projective spectrum. -/
theorem projMapMap_preimage_basicOpen
    (psi : calA →+*ᵍ calB) {f : A} {d : Nat} (hd : 0 < d) (hf : f ∈ calA d) :
    (projMapDomain psi).ι ''ᵁ (projMapMap psi ⁻¹ᵁ Proj.basicOpen calA f) =
      Proj.basicOpen calB (psi f) := sorry

/-- On a positive homogeneous basic open, the canonical projective-spectrum map is induced by
the corresponding map of homogeneous localizations. -/
theorem projMapMap_basicOpenIsoSpec_inv_comp
    (psi : calA →+*ᵍ calB) {f : A} {d : Nat} (hd : 0 < d) (hf : f ∈ calA d) :
    (Proj.basicOpenIsoSpec calB (psi f) (psi.2 hf) hd).inv ≫
        (Proj calB).homOfLE (basicOpen_le_projMapDomain psi hd hf) ≫
          projMapMap psi =
      Spec.map (CommRingCat.ofHom (Away.map psi f)) ≫
        Proj.awayι calA f hf hd := sorry

/-- A morphism from the natural domain of a graded map is the canonical projective-spectrum map
when it has the prescribed homogeneous-localization formula on every positive basic open. -/
theorem projMapMap_unique
    (psi : calA →+*ᵍ calB) (map : (projMapDomain psi).toScheme ⟶ Proj calA)
    (hmap : forall {f : A} {d : Nat} (hd : 0 < d) (hf : f ∈ calA d),
      (Proj.basicOpenIsoSpec calB (psi f) (psi.2 hf) hd).inv ≫
          (Proj calB).homOfLE (basicOpen_le_projMapDomain psi hd hf) ≫ map =
        Spec.map (CommRingCat.ofHom (Away.map psi f)) ≫ Proj.awayι calA f hf hd) :
    map = projMapMap psi := sorry

end

end AlgebraicGeometry
