import Lean
namespace CategoryTheory

/-- The data of a category consists of:
    · a u-set `Obj` of objects
    · for any pair of objects `A B`, a v-set `A⟶B` of arrows.
      (the collection of v-sets of arrows is a v+1-set)
    · a composition operation `⊚` between composable arrows
    · an identity for each object.
-/
class Category.{u, v} (Obj : Type u)  : Type max u (v + 1) where
  Hom : Obj → Obj → Type v
  comp  : ∀{A B C : Obj}, Hom B C → Hom A B → Hom A C
  id    : ∀{A : Obj}, Hom A A
  comp_assoc : ∀{A B C D : Obj} (h : Hom C D) (g : Hom B C) (f : Hom A B),
    comp (comp h g) f =  comp h (comp g f)
  id_comp : ∀{A B : Obj} (f : Hom A B), comp id f = f
  comp_id : ∀{A B : Obj} (f : Hom A B), comp f id = f

/-- Notation for hom-sets, composition, and identites. -/
infixl:10 "⟶" => Category.Hom --type as ``\-->``
infixl:80 "⊚" => Category.comp -- type as \oo
scoped notation "𝟙" => Category.id  -- type as ``\b1``
abbrev comp_assoc (Obj : Type u) [Category Obj] {A B C D : Obj} (h : C⟶D) (g : B⟶C) (f : A⟶B) :=
  @Category.comp_assoc Obj _ _ _ _ _ h g f
abbrev id_comp (Obj : Type u) [Category Obj] {A B : Obj} (f : A⟶B) :=
  @Category.id_comp Obj _ _ _ f
abbrev comp_id (Obj : Type u) [Category Obj] {A B : Obj} (f : A⟶B) :=
  @Category.comp_id Obj _ _ _ f


variable {C : Type u} [Category.{u, v} C]


/-- If an arrow `X⟶X` is a one-sided identity, then it must be `𝟙`. -/
theorem unique_identity : ∀(X : C) (id' : X⟶X),  (∀{A : C} (f : A⟶X), f = id' ⊚ f)
  ∨ (∀{A : C} (f : X⟶A), f = f ⊚ id' ) → id' = 𝟙 := by
  intro X id' hor; apply Or.elim hor
  · intro hor; rw[hor 𝟙, comp_id C id']
  · intro hor; rw[hor 𝟙, id_comp C id']

/--Monic, Epi, and Iso Arrows. -/
class Monic {X Y : C} (f : X⟶Y) : Prop where pf : ∀(Z : C) (g h : Z⟶X),  f ⊚ g = f ⊚ h → g = h
def Epi   {X Y: C} (f : X⟶Y) : Prop :=  ∀(Z : C) (g h : Y⟶Z), g ⊚ f = h ⊚ f → g = h
class Iso   {X Y : C} (f : X⟶Y) : Prop where pf : ∃(g : Y⟶X), f ⊚ g = 𝟙 ∧ g ⊚ f = 𝟙


instance {X Y : C} (f : X⟶Y) : [Iso f] → Monic f := by
  intro iso;
  apply Exists.elim iso.pf; intro f.inv h_and;
  apply Monic.mk; intro Z g h h_eq
  have h_inv :  f.inv ⊚ (f⊚g) =  f.inv ⊚ (f⊚h) := by rw[h_eq]
  rw [← comp_assoc C f.inv f g, ← comp_assoc C f.inv f h, And.right h_and, id_comp, id_comp] at h_inv
  exact h_inv

variable {X Y : C} (f : X⟶Y) [Iso f]

theorem inst : Monic f := by infer_instance








  --rw[← Category.comp_assoc f.inv (f⊚g)] at this
