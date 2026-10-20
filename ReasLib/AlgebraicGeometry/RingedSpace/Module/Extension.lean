module

public import Mathlib.CategoryTheory.EssentialImage
public import Mathlib.Topology.Sheaves.LocallySurjective
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Definition

/-!
# Mixed-scalar extensions of modules along a morphism of ringed spaces

A mixed-scalar module extension along `i : X ⟶ X'` consists of modules on `X`
and `X'`, maps between their pushforward endpoints, and a short-exactness
certificate for the resulting short complex.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.RingedSpace
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.Hom

variable {X X' : RingedSpace.{u}} (i : X ⟶ X')

/-- A short exact sequence of `𝒪_{X'}`-modules whose endpoints are pushforwards
of `𝒪_X`-modules along `i`. -/
abbrev ModuleExtension :=
  Σ kernel : X.Modules, Σ cokernel : X.Modules, Σ middle : X'.Modules,
    { maps : ((pushforward i).obj kernel ⟶ middle) ×
        (middle ⟶ (pushforward i).obj cokernel) //
      ∃ zero : maps.1 ≫ maps.2 = 0,
        (ShortComplex.mk maps.1 maps.2 zero).ShortExact }

namespace ModuleExtension

variable {i}

/-- Assemble a mixed-scalar module extension from its modules, maps, and exactness witness. -/
def mk (kernel cokernel : X.Modules) (middle : X'.Modules)
    (ι : (pushforward i).obj kernel ⟶ middle)
    (π : middle ⟶ (pushforward i).obj cokernel)
    (zero : ι ≫ π = 0)
    (shortExact : (ShortComplex.mk ι π zero).ShortExact) :
    ModuleExtension i :=
  ⟨kernel, cokernel, middle, ⟨(ι, π), ⟨zero, shortExact⟩⟩⟩

/-- The kernel module on the source ringed space. -/
abbrev kernel (E : ModuleExtension i) : X.Modules :=
  E.1

/-- The cokernel module on the source ringed space. -/
abbrev cokernel (E : ModuleExtension i) : X.Modules :=
  E.2.1

/-- The middle module on the target ringed space. -/
abbrev middle (E : ModuleExtension i) : X'.Modules :=
  E.2.2.1

/-- The inclusion from the pushforward of the kernel module. -/
abbrev ι (E : ModuleExtension i) :
    (pushforward i).obj E.kernel ⟶ E.middle :=
  E.2.2.2.1.1

/-- The projection to the pushforward of the cokernel module. -/
abbrev π (E : ModuleExtension i) :
    E.middle ⟶ (pushforward i).obj E.cokernel :=
  E.2.2.2.1.2

/-- The zero composite of the two maps. -/
def zero (E : ModuleExtension i) : E.ι ≫ E.π = 0 :=
  E.2.2.2.2.choose

/-- The short-exactness certificate of the displayed sequence. -/
def shortExact (E : ModuleExtension i) :
    (ShortComplex.mk E.ι E.π E.zero).ShortExact :=
  E.2.2.2.2.choose_spec

/-- The short complex `i _* 𝒦 ⟶ ℱ' ⟶ i _* ℱ` of `𝒪_{X'}`-modules. -/
abbrev toShortComplex (E : ModuleExtension i) : ShortComplex X'.Modules :=
  ShortComplex.mk E.ι E.π E.zero

/-- Rebuild a mixed-scalar module extension from a short complex of `𝒪_{X'}`-modules
together with identifications of its endpoints with pushforwards of `𝒪_X`-modules. -/
def ofShortComplex {kernel cokernel : X.Modules} {S : ShortComplex X'.Modules}
    (e₁ : (pushforward i).obj kernel ≅ S.X₁)
    (e₃ : (pushforward i).obj cokernel ≅ S.X₃)
    (zero : (e₁.hom ≫ S.f) ≫ (S.g ≫ e₃.inv) = 0)
    (hSE : (ShortComplex.mk (e₁.hom ≫ S.f) (S.g ≫ e₃.inv) zero).ShortExact) :
    ModuleExtension i :=
  mk kernel cokernel S.X₂ (e₁.hom ≫ S.f) (S.g ≫ e₃.inv) zero hSE

/-- A short complex of `𝒪_{X'}`-modules is isomorphic to one arising from a
mixed-scalar module extension exactly when it is short exact and both endpoints
belong to the essential image of the pushforward functor. -/
theorem mem_essImage_iff
    (h_closed : Topology.IsClosedEmbedding i.hom.base)
    [Sheaf.IsLocallySurjective (commRingSheafPushforwardMap i)]
    (S : ShortComplex X'.Modules) :
    (∃ E : ModuleExtension i, Nonempty (E.toShortComplex ≅ S)) ↔
      S.ShortExact ∧ (pushforward i).essImage S.X₁ ∧ (pushforward i).essImage S.X₃ :=
  sorry

end ModuleExtension

end AlgebraicGeometry.RingedSpace.Hom
