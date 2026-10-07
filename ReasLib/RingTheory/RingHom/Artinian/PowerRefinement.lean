module

public import Mathlib.RingTheory.Artinian.Ring
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Algebra.CharP.RingHom
public import ReasLib.RingTheory.RingHom.Local.MaximalIdeal
public import ReasLib.RingTheory.RingHom.PowerImage
public import ReasLib.RingTheory.Smooth.EssSmooth

@[expose] public section

/-!
# Artinian power refinements of ring homomorphisms

This leaf owns the presentation-independent ring-map core of positive-power
refinement. The data type itself imposes only the assumptions needed by its
fields; endpoint Artinian and local hypotheses enter only the existence and
locality API.
-/

universe u v w

namespace RingHom.Artinian

/-- An essentially smooth Artinian-local refinement of a ring map that
captures a positive power of a chosen target element. -/
@[stacks 07FI "local Artinian power refinement datum"]
structure PowerRefinement
    {D : Type u} {T : Type v} [CommRing D] [CommRing T]
    (f : D →+* T) (t : T) where
  /-- The positive exponent captured by the refinement. -/
  exponent : ℕ+
  /-- The intermediate Artinian local ring. -/
  mid : Type w
  /-- The commutative-ring structure on the intermediate ring. -/
  instCommRing : CommRing mid
  /-- The intermediate ring is Artinian. -/
  instArtinian : IsArtinianRing mid
  /-- The intermediate ring is local. -/
  instLocal : IsLocalRing mid
  /-- The map from the source to the intermediate ring. -/
  fromSource : D →+* mid
  /-- The map from the intermediate ring to the target. -/
  toTarget : mid →+* T
  /-- The refinement maps factor the original map. -/
  factor : toTarget.comp fromSource = f
  /-- The first refinement map is essentially smooth. -/
  smooth : fromSource.EssSmooth
  /-- The second refinement map is flat. -/
  flat : toTarget.Flat
  /-- The chosen power of the target element lies in the intermediate image. -/
  power_mem : PowerImage.InRange toTarget t exponent

attribute [instance] PowerRefinement.instCommRing PowerRefinement.instArtinian
  PowerRefinement.instLocal

namespace PowerRefinement

variable {D : Type u} {T : Type v} [CommRing D] [CommRing T]
variable {f : D →+* T} {t : T}

/-- Build an Artinian power refinement directly from its two maps and the
factorization, smoothness, flatness, and power-range conditions. -/
def ofMaps {B : Type w} [CommRing B] [IsArtinianRing B] [IsLocalRing B]
    (e : ℕ+) (g : D →+* B) (h : B →+* T)
    (hfactor : h.comp g = f) (hsmooth : g.EssSmooth) (hflat : h.Flat)
    (hpower : PowerImage.InRange h t e) :
    PowerRefinement.{u, v, w} f t where
  exponent := e
  mid := B
  instCommRing := inferInstance
  instArtinian := inferInstance
  instLocal := inferInstance
  fromSource := g
  toTarget := h
  factor := hfactor
  smooth := hsmooth
  flat := hflat
  power_mem := hpower

/-- The direct constructor preserves the selected exponent. -/
@[simp]
theorem exponent_ofMaps {B : Type w} [CommRing B] [IsArtinianRing B]
    [IsLocalRing B] (e : ℕ+) (g : D →+* B) (h : B →+* T)
    (hfactor : h.comp g = f) (hsmooth : g.EssSmooth) (hflat : h.Flat)
    (hpower : PowerImage.InRange h t e) :
    (ofMaps e g h hfactor hsmooth hflat hpower).exponent = e := sorry

/-- The source projection of the direct constructor is the supplied source
map. -/
@[simp]
theorem fromSource_ofMaps {B : Type w} [CommRing B] [IsArtinianRing B]
    [IsLocalRing B] (e : ℕ+) (g : D →+* B) (h : B →+* T)
    (hfactor : h.comp g = f) (hsmooth : g.EssSmooth) (hflat : h.Flat)
    (hpower : PowerImage.InRange h t e) :
    (ofMaps e g h hfactor hsmooth hflat hpower).fromSource = g := sorry

/-- The target projection of the direct constructor is the supplied target
map. -/
@[simp]
theorem toTarget_ofMaps {B : Type w} [CommRing B] [IsArtinianRing B]
    [IsLocalRing B] (e : ℕ+) (g : D →+* B) (h : B →+* T)
    (hfactor : h.comp g = f) (hsmooth : g.EssSmooth) (hflat : h.Flat)
    (hpower : PowerImage.InRange h t e) :
    (ofMaps e g h hfactor hsmooth hflat hpower).toTarget = h := sorry

namespace mid

/-- The intermediate ring inherits every prime characteristic of the source. -/
@[stacks 07FI "prime characteristic of a local Artinian refinement"]
instance charP {p : ℕ} [Fact p.Prime] [CharP D p]
    (P : PowerRefinement.{u, v, w} f t) : CharP P.mid p := sorry

end mid

namespace fromSource

/-- The source map of an Artinian power refinement is local when its source
is Artinian local. -/
@[stacks 07FI "locality of the source refinement map"]
instance isLocal [IsArtinianRing D] [IsLocalRing D]
    (P : PowerRefinement.{u, v, w} f t) : IsLocalHom P.fromSource := sorry

end fromSource

namespace toTarget

/-- The target map of an Artinian power refinement is local whenever its
target is nontrivial. -/
@[stacks 07FI "locality of the target refinement map"]
instance isLocal [Nontrivial T] (P : PowerRefinement.{u, v, w} f t) :
    IsLocalHom P.toTarget := sorry

end toTarget

/-- The conditions stored by an Artinian power refinement, without adding
unnecessary hypotheses on its endpoints. -/
@[stacks 07FI "local Artinian power refinement specification"]
theorem spec (P : PowerRefinement.{u, v, w} f t) :
    IsArtinianRing P.mid ∧
      IsLocalRing P.mid ∧
      P.toTarget.comp P.fromSource = f ∧
      P.fromSource.EssSmooth ∧
      P.toTarget.Flat ∧
      PowerImage.InRange P.toTarget t P.exponent := sorry

/-- Both maps of an Artinian power refinement are local under the minimal
endpoint hypotheses. -/
theorem local_spec [IsArtinianRing D] [IsLocalRing D] [Nontrivial T]
    (P : PowerRefinement.{u, v, w} f t) :
    IsLocalHom P.fromSource ∧ IsLocalHom P.toTarget := sorry

/-- A flat map of Artinian local rings in positive prime characteristic has a
power refinement for every target element. -/
@[stacks 07FI "existence of a local Artinian power refinement"]
theorem nonempty [IsArtinianRing D] [IsLocalRing D]
    [IsArtinianRing T] [IsLocalRing T]
    {p : ℕ} [Fact p.Prime] [CharP D p]
    (f : D →+* T) (hflat : f.Flat) (t : T) :
    Nonempty (PowerRefinement.{u, v, max u v} f t) := sorry

end PowerRefinement

end RingHom.Artinian
