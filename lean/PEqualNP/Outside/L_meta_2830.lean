import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.List.Perm.Basic
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Push
import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_2830
open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity
abbrev V9 := Fin 9 → Bool
abbrev F9 := V9 → Bool
def maskToV (m : Nat) : V9 := fun i => m.testBit i.1
def varF (v : Fin 9) : F9 := fun x => x v
def w9F : F9 := fun x => x 0 || x 1
def projV (v : Fin 9) (f : F9) : F9 := fun x => f (fun i => if i = v then false else x i)
def permF (π : Fin 9 → Fin 9) (f : F9) : F9 := fun x => f (fun i => x (π i))
def IsMono (f : F9) : Prop :=
  ∀ x y : V9, (∀ i, x i = true → y i = true) → f x = true → f y = true
lemma isMono_varF (v : Fin 9) : IsMono (varF v) := fun _ _ hxy h => hxy v h
lemma isMono_w9F : IsMono w9F := by
  intro x y hxy h
  simp only [w9F, Bool.or_eq_true] at h ⊢
  exact h.elim (fun h0 => Or.inl (hxy 0 h0)) (fun h1 => Or.inr (hxy 1 h1))
def agrees (pos neg : List Nat) (f : F9) : Prop :=
  (∀ m ∈ pos, f (maskToV m) = true) ∧ (∀ m ∈ neg, f (maskToV m) = false)
def dominates (pos neg : List Nat) (g w : F9) : Prop :=
  (∀ m ∈ pos, g (maskToV m) = true → w (maskToV m) = true) ∧
  (∀ m ∈ neg, w (maskToV m) = true → g (maskToV m) = true)
lemma dominates_refl (pos neg : List Nat) (f : F9) : dominates pos neg f f :=
  ⟨fun _ _ h => h, fun _ _ h => h⟩
lemma dominates_and {pos neg : List Nat} {a a' b b' : F9}
    (ha : dominates pos neg a a') (hb : dominates pos neg b b') :
    dominates pos neg (fun x => a x && b x) (fun x => a' x && b' x) := by
  refine ⟨fun m hm h => ?_, fun m hm h => ?_⟩
  · simp only [Bool.and_eq_true] at h ⊢
    exact ⟨ha.1 m hm h.1, hb.1 m hm h.2⟩
  · simp only [Bool.and_eq_true] at h ⊢
    exact ⟨ha.2 m hm h.1, hb.2 m hm h.2⟩
lemma dominates_or {pos neg : List Nat} {a a' b b' : F9}
    (ha : dominates pos neg a a') (hb : dominates pos neg b b') :
    dominates pos neg (fun x => a x || b x) (fun x => a' x || b' x) := by
  refine ⟨fun m hm h => ?_, fun m hm h => ?_⟩
  · simp only [Bool.or_eq_true] at h ⊢
    exact h.elim (fun h1 => Or.inl (ha.1 m hm h1)) (fun h2 => Or.inr (hb.1 m hm h2))
  · simp only [Bool.or_eq_true] at h ⊢
    exact h.elim (fun h1 => Or.inl (ha.2 m hm h1)) (fun h2 => Or.inr (hb.2 m hm h2))
lemma agrees_of_dom {pos neg : List Nat} {f f' : F9}
    (hf : agrees pos neg f) (hd : dominates pos neg f f') : agrees pos neg f' := by
  refine ⟨fun m hm => hd.1 m hm (hf.1 m hm), fun m hm => ?_⟩
  cases h : f' (maskToV m)
  · rfl
  · have h1 := hd.2 m hm h
    rw [hf.2 m hm] at h1
    contradiction
def MonoReach : Nat → List F9 → F9 → Prop
  | 0, W, f => f ∈ W ∨ f = fun _ => false
  | k + 1, W, f =>
      MonoReach k W f ∨
      MonoReach k ((fun _ => false) :: W) f ∨
      MonoReach k ((fun _ => true) :: W) f ∨
      (∃ a ∈ W, ∃ b ∈ W, MonoReach k ((fun x => a x && b x) :: W) f) ∨
      (∃ a ∈ W, ∃ b ∈ W, MonoReach k ((fun x => a x || b x) :: W) f)
lemma monoReach_mono {k : Nat} {W W' : List F9} {f : F9}
    (hsub : ∀ w ∈ W, w ∈ W') (h : MonoReach k W f) : MonoReach k W' f := by
  induction k generalizing W W' with
  | zero =>
    rcases h with hw | rfl
    · exact Or.inl (hsub _ hw)
    · exact Or.inr rfl
  | succ k ih =>
    rcases h with h1 | h2 | h3 | ⟨a, ha, b, hb, h4⟩ | ⟨a, ha, b, hb, h5⟩
    · exact Or.inl (ih hsub h1)
    · exact Or.inr (Or.inl (ih (fun w hw => by rcases List.mem_cons.1 hw with rfl | hw; exact List.mem_cons_self; exact List.mem_cons_of_mem _ (hsub _ hw)) h2))
    · exact Or.inr (Or.inr (Or.inl (ih (fun w hw => by rcases List.mem_cons.1 hw with rfl | hw; exact List.mem_cons_self; exact List.mem_cons_of_mem _ (hsub _ hw)) h3)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨a, hsub _ ha, b, hsub _ hb, ih (fun w hw => by rcases List.mem_cons.1 hw with rfl | hw; exact List.mem_cons_self; exact List.mem_cons_of_mem _ (hsub _ hw)) h4⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨a, hsub _ ha, b, hsub _ hb, ih (fun w hw => by rcases List.mem_cons.1 hw with rfl | hw; exact List.mem_cons_self; exact List.mem_cons_of_mem _ (hsub _ hw)) h5⟩)))
lemma monoReach_le {k k' : Nat} {W : List F9} {f : F9} (hle : k ≤ k') (h : MonoReach k W f) :
    MonoReach k' W f := by
  induction k', hle using Nat.le_induction with
  | base => exact h
  | succ _ _ ih => exact Or.inl ih
lemma monoReach_isMono {k : Nat} {W : List F9} {f : F9}
    (hW : ∀ w ∈ W, IsMono w) (h : MonoReach k W f) : IsMono f := by
  induction k generalizing W with
  | zero =>
    rcases h with hw | rfl
    · exact hW _ hw
    · intro _ _ _ h1; contradiction
  | succ k ih =>
    rcases h with h1 | h2 | h3 | ⟨a, ha, b, hb, h4⟩ | ⟨a, ha, b, hb, h5⟩
    · exact ih hW h1
    · refine ih (fun w hw => ?_) h2
      rcases List.mem_cons.1 hw with rfl | hw
      · intro _ _ _ h1; contradiction
      · exact hW _ hw
    · refine ih (fun w hw => ?_) h3
      rcases List.mem_cons.1 hw with rfl | hw
      · intro _ _ _ _; rfl
      · exact hW _ hw
    · refine ih (fun w hw => ?_) h4
      rcases List.mem_cons.1 hw with rfl | hw
      · intro x y hxy h1
        simp only [Bool.and_eq_true] at h1 ⊢
        exact ⟨hW a ha x y hxy h1.1, hW b hb x y hxy h1.2⟩
      · exact hW _ hw
    · refine ih (fun w hw => ?_) h5
      rcases List.mem_cons.1 hw with rfl | hw
      · intro x y hxy h1
        simp only [Bool.or_eq_true] at h1 ⊢
        exact h1.elim (fun h' => Or.inl (hW a ha x y hxy h')) (fun h' => Or.inr (hW b hb x y hxy h'))
      · exact hW _ hw
lemma monoReach_projV {k : Nat} {W : List F9} {f : F9} (v : Fin 9)
    (h : MonoReach k W f) : MonoReach k (W.map (projV v)) (projV v f) := by
  induction k generalizing W with
  | zero =>
    rcases h with hw | rfl
    · exact Or.inl (List.mem_map_of_mem hw)
    · exact Or.inr rfl
  | succ k ih =>
    rcases h with h1 | h2 | h3 | ⟨a, ha, b, hb, h4⟩ | ⟨a, ha, b, hb, h5⟩
    · exact Or.inl (ih h1)
    · have h2' := ih h2; exact Or.inr (Or.inl h2')
    · have h3' := ih h3; exact Or.inr (Or.inr (Or.inl h3'))
    · have h4' := ih h4; exact Or.inr (Or.inr (Or.inr (Or.inl ⟨projV v a, List.mem_map_of_mem ha, projV v b, List.mem_map_of_mem hb, h4'⟩)))
    · have h5' := ih h5; exact Or.inr (Or.inr (Or.inr (Or.inr ⟨projV v a, List.mem_map_of_mem ha, projV v b, List.mem_map_of_mem hb, h5'⟩)))
lemma monoReach_permF {k : Nat} {W : List F9} {f : F9} (π : Fin 9 → Fin 9)
    (h : MonoReach k W f) : MonoReach k (W.map (permF π)) (permF π f) := by
  induction k generalizing W with
  | zero =>
    rcases h with hw | rfl
    · exact Or.inl (List.mem_map_of_mem hw)
    · exact Or.inr rfl
  | succ k ih =>
    rcases h with h1 | h2 | h3 | ⟨a, ha, b, hb, h4⟩ | ⟨a, ha, b, hb, h5⟩
    · exact Or.inl (ih h1)
    · exact Or.inr (Or.inl (ih h2))
    · exact Or.inr (Or.inr (Or.inl (ih h3)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨permF π a, List.mem_map_of_mem ha, permF π b, List.mem_map_of_mem hb, ih h4⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨permF π a, List.mem_map_of_mem ha, permF π b, List.mem_map_of_mem hb, ih h5⟩)))
lemma monoReach_drop_false {k : Nat} {W : List F9} {f : F9}
    (h : MonoReach k ((fun _ => false) :: W) f) : MonoReach k W f := by
  induction k generalizing W with
  | zero =>
    rcases h with hw | rfl
    · rcases List.mem_cons.1 hw with rfl | hw
      · exact Or.inr rfl
      · exact Or.inl hw
    · exact Or.inr rfl
  | succ k ih =>
    rcases h with h1 | h2 | h3 | ⟨a, ha, b, hb, h4⟩ | ⟨a, ha, b, hb, h5⟩
    · exact Or.inl (ih h1)
    · exact Or.inl (ih (monoReach_mono (fun w hw => by rcases List.mem_cons.1 hw with rfl | hw; exact List.mem_cons_self; exact hw) h2))
    · exact Or.inr (Or.inr (Or.inl (ih (monoReach_mono (fun w hw => by
        rcases List.mem_cons.1 hw with rfl | hw
        · exact List.mem_cons_of_mem _ List.mem_cons_self
        · rcases List.mem_cons.1 hw with rfl | hw
          · exact List.mem_cons_self
          · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hw)) h3))))
    · rcases List.mem_cons.1 ha with rfl | ha <;> rcases List.mem_cons.1 hb with rfl | hb
      · exact Or.inl (ih (monoReach_mono (fun w hw => by rcases List.mem_cons.1 hw with rfl | hw; exact List.mem_cons_self; exact hw) (by simpa using h4)))
      · exact Or.inl (ih (monoReach_mono (fun w hw => by rcases List.mem_cons.1 hw with rfl | hw; exact List.mem_cons_self; exact hw) (by simpa using h4)))
      · exact Or.inl (ih (monoReach_mono (fun w hw => by rcases List.mem_cons.1 hw with rfl | hw; exact List.mem_cons_self; exact hw) (by simpa using h4)))
      · refine Or.inr (Or.inr (Or.inr (Or.inl ⟨a, ha, b, hb, ih (monoReach_mono (fun w hw => ?_) h4)⟩)))
        rcases List.mem_cons.1 hw with rfl | hw
        · exact List.mem_cons_of_mem _ List.mem_cons_self
        · rcases List.mem_cons.1 hw with rfl | hw
          · exact List.mem_cons_self
          · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hw)
    · rcases List.mem_cons.1 ha with rfl | ha <;> rcases List.mem_cons.1 hb with rfl | hb
      · exact Or.inl (ih (monoReach_mono (fun w hw => by rcases List.mem_cons.1 hw with rfl | hw; exact List.mem_cons_self; exact hw) (by simpa using h5)))
      · exact Or.inl (ih (monoReach_mono (fun w hw => by rcases List.mem_cons.1 hw with rfl | hw; exact List.mem_cons_of_mem _ hb; exact hw) (by simpa using h5)))
      · exact Or.inl (ih (monoReach_mono (fun w hw => by rcases List.mem_cons.1 hw with rfl | hw; exact List.mem_cons_of_mem _ ha; exact hw) (by simpa using h5)))
      · refine Or.inr (Or.inr (Or.inr (Or.inr ⟨a, ha, b, hb, ih (monoReach_mono (fun w hw => ?_) h5)⟩)))
        rcases List.mem_cons.1 hw with rfl | hw
        · exact List.mem_cons_of_mem _ List.mem_cons_self
        · rcases List.mem_cons.1 hw with rfl | hw
          · exact List.mem_cons_self
          · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hw)
lemma monoReach_drop_true {k : Nat} {W : List F9} {f : F9}
    (h : MonoReach k ((fun _ => true) :: W) f) : f = (fun _ => true) ∨ MonoReach k W f := by
  induction k generalizing W with
  | zero =>
    rcases h with hw | rfl
    · rcases List.mem_cons.1 hw with rfl | hw
      · exact Or.inl rfl
      · exact Or.inr (Or.inl hw)
    · exact Or.inr (Or.inr rfl)
  | succ k ih =>
    rcases h with h1 | h2 | h3 | ⟨a, ha, b, hb, h4⟩ | ⟨a, ha, b, hb, h5⟩
    · exact (ih h1).elim Or.inl (fun h' => Or.inr (Or.inl h'))
    · have h2' : MonoReach k ((fun _ => true) :: (fun _ => false) :: W) f :=
        monoReach_mono (fun w hw => by
          rcases List.mem_cons.1 hw with rfl | hw
          · exact List.mem_cons_of_mem _ List.mem_cons_self
          · rcases List.mem_cons.1 hw with rfl | hw
            · exact List.mem_cons_self
            · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hw)) h2
      exact (ih h2').elim Or.inl (fun h' => Or.inr (Or.inr (Or.inl h')))
    · have h3' : MonoReach k ((fun _ => true) :: W) f :=
        monoReach_mono (fun w hw => by rcases List.mem_cons.1 hw with rfl | hw; exact List.mem_cons_self; exact hw) h3
      exact (ih h3').elim Or.inl (fun h' => Or.inr (Or.inl h'))
    · rcases List.mem_cons.1 ha with rfl | ha <;> rcases List.mem_cons.1 hb with rfl | hb
      · exact (ih (monoReach_mono (fun w hw => by rcases List.mem_cons.1 hw with rfl | hw; exact List.mem_cons_self; exact hw) (by simpa using h4))).elim Or.inl (fun h' => Or.inr (Or.inl h'))
      · exact (ih (monoReach_mono (fun w hw => by rcases List.mem_cons.1 hw with rfl | hw; exact List.mem_cons_of_mem _ hb; exact hw) (by simpa using h4))).elim Or.inl (fun h' => Or.inr (Or.inl h'))
      · exact (ih (monoReach_mono (fun w hw => by rcases List.mem_cons.1 hw with rfl | hw; exact List.mem_cons_of_mem _ ha; exact hw) (by simpa using h4))).elim Or.inl (fun h' => Or.inr (Or.inl h'))
      · have h4' : MonoReach k ((fun _ => true) :: (fun x => a x && b x) :: W) f :=
          monoReach_mono (fun w hw => by
            rcases List.mem_cons.1 hw with rfl | hw
            · exact List.mem_cons_of_mem _ List.mem_cons_self
            · rcases List.mem_cons.1 hw with rfl | hw
              · exact List.mem_cons_self
              · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hw)) h4
        exact (ih h4').elim Or.inl (fun h' => Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨a, ha, b, hb, h'⟩)))))
    · rcases List.mem_cons.1 ha with rfl | ha <;> rcases List.mem_cons.1 hb with rfl | hb
      · exact (ih (monoReach_mono (fun w hw => by rcases List.mem_cons.1 hw with rfl | hw; exact List.mem_cons_self; exact hw) (by simpa using h5))).elim Or.inl (fun h' => Or.inr (Or.inl h'))
      · exact (ih (monoReach_mono (fun w hw => by rcases List.mem_cons.1 hw with rfl | hw; exact List.mem_cons_self; exact hw) (by simpa using h5))).elim Or.inl (fun h' => Or.inr (Or.inl h'))
      · exact (ih (monoReach_mono (fun w hw => by rcases List.mem_cons.1 hw with rfl | hw; exact List.mem_cons_self; exact hw) (by simpa using h5))).elim Or.inl (fun h' => Or.inr (Or.inl h'))
      · have h5' : MonoReach k ((fun _ => true) :: (fun x => a x || b x) :: W) f :=
          monoReach_mono (fun w hw => by
            rcases List.mem_cons.1 hw with rfl | hw
            · exact List.mem_cons_of_mem _ List.mem_cons_self
            · rcases List.mem_cons.1 hw with rfl | hw
              · exact List.mem_cons_self
              · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hw)) h5
        exact (ih h5').elim Or.inl (fun h' => Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨a, ha, b, hb, h'⟩)))))
lemma monoReach_dom {pos neg : List Nat} {k : Nat} {W1 W2 : List F9} {f : F9}
    (hdom : ∀ u ∈ W1, ∃ v ∈ W2, dominates pos neg u v)
    (h : MonoReach k W1 f) : ∃ f', MonoReach k W2 f' ∧ dominates pos neg f f' := by
  induction k generalizing W1 W2 with
  | zero =>
    rcases h with hw | rfl
    · obtain ⟨v, hv, hd⟩ := hdom _ hw
      exact ⟨v, Or.inl hv, hd⟩
    · exact ⟨fun _ => false, Or.inr rfl, dominates_refl pos neg _⟩
  | succ k ih =>
    rcases h with h1 | h2 | h3 | ⟨a, ha, b, hb, h4⟩ | ⟨a, ha, b, hb, h5⟩
    · obtain ⟨f', hf', hd⟩ := ih hdom h1
      exact ⟨f', Or.inl hf', hd⟩
    · have hdom' : ∀ u ∈ (fun _ => false) :: W1, ∃ v ∈ (fun _ => false) :: W2, dominates pos neg u v := by
        intro u hu; rcases List.mem_cons.1 hu with rfl | hu
        · exact ⟨_, List.mem_cons_self, dominates_refl pos neg _⟩
        · obtain ⟨v, hv, hd⟩ := hdom u hu; exact ⟨v, List.mem_cons_of_mem _ hv, hd⟩
      obtain ⟨f', hf', hd⟩ := ih hdom' h2
      exact ⟨f', Or.inr (Or.inl hf'), hd⟩
    · have hdom' : ∀ u ∈ (fun _ => true) :: W1, ∃ v ∈ (fun _ => true) :: W2, dominates pos neg u v := by
        intro u hu; rcases List.mem_cons.1 hu with rfl | hu
        · exact ⟨_, List.mem_cons_self, dominates_refl pos neg _⟩
        · obtain ⟨v, hv, hd⟩ := hdom u hu; exact ⟨v, List.mem_cons_of_mem _ hv, hd⟩
      obtain ⟨f', hf', hd⟩ := ih hdom' h3
      exact ⟨f', Or.inr (Or.inr (Or.inl hf')), hd⟩
    · obtain ⟨a', ha', hda⟩ := hdom a ha
      obtain ⟨b', hb', hdb⟩ := hdom b hb
      have hdom' : ∀ u ∈ (fun x => a x && b x) :: W1, ∃ v ∈ (fun x => a' x && b' x) :: W2, dominates pos neg u v := by
        intro u hu; rcases List.mem_cons.1 hu with rfl | hu
        · exact ⟨_, List.mem_cons_self, dominates_and hda hdb⟩
        · obtain ⟨v, hv, hd⟩ := hdom u hu; exact ⟨v, List.mem_cons_of_mem _ hv, hd⟩
      obtain ⟨f', hf', hd⟩ := ih hdom' h4
      exact ⟨f', Or.inr (Or.inr (Or.inr (Or.inl ⟨a', ha', b', hb', hf'⟩))), hd⟩
    · obtain ⟨a', ha', hda⟩ := hdom a ha
      obtain ⟨b', hb', hdb⟩ := hdom b hb
      have hdom' : ∀ u ∈ (fun x => a x || b x) :: W1, ∃ v ∈ (fun x => a' x || b' x) :: W2, dominates pos neg u v := by
        intro u hu; rcases List.mem_cons.1 hu with rfl | hu
        · exact ⟨_, List.mem_cons_self, dominates_or hda hdb⟩
        · obtain ⟨v, hv, hd⟩ := hdom u hu; exact ⟨v, List.mem_cons_of_mem _ hv, hd⟩
      obtain ⟨f', hf', hd⟩ := ih hdom' h5
      exact ⟨f', Or.inr (Or.inr (Or.inr (Or.inr ⟨a', ha', b', hb', hf'⟩))), hd⟩
def HasMono (pos neg : List Nat) (W : List F9) (k : Nat) : Prop :=
  ∃ f, MonoReach k W f ∧ agrees pos neg f
lemma hasMono_mono_W {pos neg : List Nat} {W W' : List F9} {k : Nat}
    (hsub : ∀ w ∈ W, w ∈ W') (h : HasMono pos neg W k) : HasMono pos neg W' k :=
  let ⟨f, hf, ha⟩ := h; ⟨f, monoReach_mono hsub hf, ha⟩
lemma hasMono_mono_k {pos neg : List Nat} {W : List F9} {k k' : Nat}
    (hle : k ≤ k') (h : HasMono pos neg W k) : HasMono pos neg W k' :=
  let ⟨f, hf, ha⟩ := h; ⟨f, monoReach_le hle hf, ha⟩
lemma hasMono_drop_false {pos neg : List Nat} {W : List F9} {k : Nat}
    (h : HasMono pos neg ((fun _ => false) :: W) k) : HasMono pos neg W k :=
  let ⟨f, hf, ha⟩ := h; ⟨f, monoReach_drop_false hf, ha⟩
lemma hasMono_drop_true {pos neg : List Nat} {W : List F9} {k : Nat}
    (hneg : neg ≠ []) (h : HasMono pos neg ((fun _ => true) :: W) k) : HasMono pos neg W k := by
  obtain ⟨f, hf, ha⟩ := h
  rcases monoReach_drop_true hf with rfl | hf'
  · cases neg with
    | nil => exact absurd rfl hneg
    | cons m _ =>
      have := ha.2 m List.mem_cons_self
      contradiction
  · exact ⟨f, hf', ha⟩
lemma hasMono_dom {pos neg : List Nat} {W1 W2 : List F9} {k : Nat}
    (hdom : ∀ u ∈ W1, ∃ v ∈ W2, dominates pos neg u v)
    (h : HasMono pos neg W1 k) : HasMono pos neg W2 k := by
  obtain ⟨f, hf, ha⟩ := h
  obtain ⟨f', hf', hd⟩ := monoReach_dom hdom hf
  exact ⟨f', hf', agrees_of_dom ha hd⟩
def evalGateF (W : List F9) (g : Gate) : F9 :=
  fun x => g.op.eval (g.inputs.map fun i => (W.getD i (fun _ => false)) x)
def runGatesF (W : List F9) : List Gate → List F9
  | [] => W
  | g :: gs => runGatesF (W ++ [evalGateF W g]) gs
lemma getD_map_eval (W : List F9) (i : Nat) (x : V9) :
    (W.map (· x)).getD i false = (W.getD i (fun _ => false)) x := by
  induction W generalizing i with
  | nil => rfl
  | cons a t ih =>
    cases i with
    | zero => rfl
    | succ i => exact ih i
lemma runGatesF_map (W : List F9) (gs : List Gate) (x : V9) :
    (runGatesF W gs).map (· x) =
      gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (W.map (· x)) := by
  induction gs generalizing W with
  | nil => rfl
  | cons g gs ih =>
    simp only [runGatesF, List.foldl_cons]
    rw [ih]
    congr 1
    simp only [List.map_append, List.map_cons, List.map_nil, evalGateF]
    congr 2; congr 1
    exact List.map_congr_left fun i _ => (getD_map_eval W i x).symm
lemma getD_mem_or_false (W : List F9) (i : Nat) :
    W.getD i (fun _ => false) ∈ W ∨ W.getD i (fun _ => false) = fun _ => false := by
  induction W generalizing i with
  | nil => exact Or.inr rfl
  | cons a t ih =>
    cases i with
    | zero => exact Or.inl List.mem_cons_self
    | succ i =>
      rcases ih i with h | h
      · exact Or.inl (List.mem_cons_of_mem _ h)
      · exact Or.inr h
lemma runGatesF_monoReach (gs : List Gate) (W : List F9) (out : Nat)
    (hM : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    MonoReach gs.length W ((runGatesF W gs).getD out (fun _ => false)) := by
  induction gs generalizing W with
  | nil =>
    exact getD_mem_or_false W out
  | cons g gs ih =>
    have hg := hM g List.mem_cons_self
    have hgs : ∀ g' ∈ gs, g'.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g'.inputs.length ≤ 2 :=
      fun g' hg' => hM g' (List.mem_cons_of_mem _ hg')
    simp only [List.length_cons, runGatesF]
    set tgt := (runGatesF (W ++ [evalGateF W g]) gs).getD out (fun _ => false)
    have hrec : MonoReach gs.length (W ++ [evalGateF W g]) tgt := ih (W ++ [evalGateF W g]) hgs
    have hrec' : MonoReach gs.length (evalGateF W g :: W) tgt :=
      monoReach_mono (fun w hw => by
        rcases List.mem_append.1 hw with hw | hw
        · exact List.mem_cons_of_mem _ hw
        · rcases List.mem_singleton.1 hw with rfl; exact List.mem_cons_self) hrec
    rcases hg with ⟨hop, hlen⟩
    have hop' : g.op = GateOp.and ∨ g.op = GateOp.or := by simpa using hop
    cases hi : g.inputs with
    | nil =>
      rcases hop' with hop | hop
      · have he : evalGateF W g = fun _ => true := by funext x; simp [evalGateF, hi, hop, GateOp.eval]
        rw [he] at hrec'; exact Or.inr (Or.inr (Or.inl hrec'))
      · have he : evalGateF W g = fun _ => false := by funext x; simp [evalGateF, hi, hop, GateOp.eval]
        rw [he] at hrec'; exact Or.inr (Or.inl hrec')
    | cons i1 t1 =>
      cases t1 with
      | nil =>
        have he : evalGateF W g = W.getD i1 (fun _ => false) := by
          funext x; rcases hop' with hop | hop <;> simp [evalGateF, hi, hop, GateOp.eval]
        rw [he] at hrec'
        rcases getD_mem_or_false W i1 with hm | hf
        · exact Or.inl (monoReach_mono (fun w hw => by rcases List.mem_cons.1 hw with rfl | hw; exact hm; exact hw) hrec')
        · rw [hf] at hrec'; exact Or.inr (Or.inl hrec')
      | cons i2 t2 =>
        cases t2 with
        | nil =>
          rcases hop' with hop | hop
          · have he : evalGateF W g = fun x => W.getD i1 (fun _ => false) x && W.getD i2 (fun _ => false) x := by
              funext x; simp [evalGateF, hi, hop, GateOp.eval]
            rw [he] at hrec'
            rcases getD_mem_or_false W i1 with h1 | h1 <;> rcases getD_mem_or_false W i2 with h2 | h2
            · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨_, h1, _, h2, hrec'⟩)))
            · rw [h2] at hrec'; simp only [Bool.and_false] at hrec'; exact Or.inr (Or.inl hrec')
            · rw [h1] at hrec'; simp only [Bool.false_and] at hrec'; exact Or.inr (Or.inl hrec')
            · rw [h1, h2] at hrec'; simp only [Bool.false_and] at hrec'; exact Or.inr (Or.inl hrec')
          · have he : evalGateF W g = fun x => W.getD i1 (fun _ => false) x || W.getD i2 (fun _ => false) x := by
              funext x; simp [evalGateF, hi, hop, GateOp.eval]
            rw [he] at hrec'
            rcases getD_mem_or_false W i1 with h1 | h1 <;> rcases getD_mem_or_false W i2 with h2 | h2
            · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨_, h1, _, h2, hrec'⟩)))
            · rw [h2] at hrec'; simp only [Bool.or_false] at hrec'
              exact Or.inl (monoReach_mono (fun w hw => by rcases List.mem_cons.1 hw with rfl | hw; exact h1; exact hw) hrec')
            · rw [h1] at hrec'; simp only [Bool.false_or] at hrec'
              exact Or.inl (monoReach_mono (fun w hw => by rcases List.mem_cons.1 hw with rfl | hw; exact h2; exact hw) hrec')
            · rw [h1, h2] at hrec'; simp only [Bool.false_or] at hrec'; exact Or.inr (Or.inl hrec')
        | cons _ _ => simp [hi] at hlen
lemma circuit_to_hasMono (C : Circuit) (W : List F9) (pos neg : List Nat) (k : Nat)
    (hM : Monotone2 C) (hsz : C.size ≤ k)
    (hpos : ∀ m ∈ pos, C.eval (W.map (· (maskToV m))) = true)
    (hneg : ∀ m ∈ neg, C.eval (W.map (· (maskToV m))) = false) :
    HasMono pos neg W k := by
  refine ⟨(runGatesF W C.gates).getD C.output (fun _ => false),
    monoReach_le hsz (runGatesF_monoReach C.gates W C.output hM), ?_⟩
  refine ⟨fun m hm => ?_, fun m hm => ?_⟩
  · rw [← getD_map_eval, runGatesF_map]; exact hpos m hm
  · rw [← getD_map_eval, runGatesF_map]; exact hneg m hm
def pullMask (π : Fin 9 → Fin 9) (m : Nat) : Nat :=
  (List.finRange 9).foldl (fun acc i => if m.testBit (π i).1 then acc ||| (1 <<< i.1) else acc) 0
lemma testBit_one_eq (k : Nat) : (1 : Nat).testBit k = decide (k = 0) := by
  cases k with
  | zero => rfl
  | succ k => simp [Nat.testBit_succ]
lemma pullMask_testBit_aux (π : Fin 9 → Fin 9) (m : Nat) (l : List (Fin 9)) (acc : Nat) (j : Fin 9) :
    (l.foldl (fun a i => if m.testBit (π i).1 then a ||| (1 <<< i.1) else a) acc).testBit j.1 =
      (acc.testBit j.1 || (j ∈ l && m.testBit (π j).1)) := by
  induction l generalizing acc with
  | nil => simp
  | cons a t ih =>
    rw [List.foldl_cons, ih]
    by_cases hja : j = a
    · subst hja
      cases hm : m.testBit (π j).1 <;> simp [Nat.testBit_or, Nat.testBit_shiftLeft, testBit_one_eq]
    · have hne : j.1 ≠ a.1 := fun h => hja (Fin.ext h)
      cases hm : m.testBit (π a).1
      · simp [hja]
      · have hbit : (1 <<< a.1).testBit j.1 = false := by
          rw [Nat.shiftLeft_eq, Nat.one_mul, Nat.testBit_two_pow]
          exact decide_eq_false (Ne.symm hne)
        simp [Nat.testBit_or, hbit, hja]
lemma pullMask_testBit (π : Fin 9 → Fin 9) (m : Nat) (j : Fin 9) :
    (pullMask π m).testBit j.1 = m.testBit (π j).1 := by
  unfold pullMask
  rw [pullMask_testBit_aux]
  simp [List.mem_finRange]
lemma maskToV_pullMask (π : Fin 9 → Fin 9) (m : Nat) :
    maskToV (pullMask π m) = fun i => maskToV m (π i) := by
  funext i; exact pullMask_testBit π m i
def MonoLive (pos neg : List Nat) : Nat → List F9 → Prop
  | 0, W => ∃ f ∈ W, agrees pos neg f
  | k + 1, W =>
      ∃ a ∈ W, ∃ b ∈ W, ∃ isOr : Bool,
        let g : F9 := if isOr then (fun x => a x || b x) else (fun x => a x && b x)
        (∃ m ∈ pos, g (maskToV m) = true) ∧
        (∃ m ∈ neg, g (maskToV m) = false) ∧
        (∀ w ∈ W, ¬ dominates pos neg g w) ∧
        MonoLive pos neg k (g :: W)
lemma hasMono_to_monoLive {pos neg : List Nat} (hpos : pos ≠ []) (hneg : neg ≠ []) :
    ∀ k W, HasMono pos neg W k → ∃ k' ≤ k, MonoLive pos neg k' W := by
  intro k
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    intro W h
    cases k with
    | zero =>
      obtain ⟨f, hf, ha⟩ := h
      rcases hf with hw | rfl
      · exact ⟨0, Nat.le_refl 0, f, hw, ha⟩
      · cases pos with
        | nil => exact absurd rfl hpos
        | cons m _ => have := ha.1 m List.mem_cons_self; contradiction
    | succ k =>
      obtain ⟨f, hf, ha⟩ := h
      rcases hf with h1 | h2 | h3 | ⟨a, haW, b, hbW, h4⟩ | ⟨a, haW, b, hbW, h5⟩
      · obtain ⟨k', hk', hm⟩ := ih k (Nat.lt_succ_self k) W ⟨f, h1, ha⟩
        exact ⟨k', Nat.le_trans hk' (Nat.le_succ k), hm⟩
      · obtain ⟨k', hk', hm⟩ := ih k (Nat.lt_succ_self k) W (hasMono_drop_false ⟨f, h2, ha⟩)
        exact ⟨k', Nat.le_trans hk' (Nat.le_succ k), hm⟩
      · obtain ⟨k', hk', hm⟩ := ih k (Nat.lt_succ_self k) W (hasMono_drop_true hneg ⟨f, h3, ha⟩)
        exact ⟨k', Nat.le_trans hk' (Nat.le_succ k), hm⟩
      · let g : F9 := fun x => a x && b x
        by_cases hgp : ∃ m ∈ pos, g (maskToV m) = true
        · by_cases hgn : ∃ m ∈ neg, g (maskToV m) = false
          · by_cases hdom : ∃ w ∈ W, dominates pos neg g w
            · obtain ⟨w, hwW, hdw⟩ := hdom
              have hW' : HasMono pos neg W k := by
                apply hasMono_dom (W1 := g :: W) _ ⟨f, h4, ha⟩
                intro u hu; rcases List.mem_cons.1 hu with rfl | hu
                · exact ⟨w, hwW, hdw⟩
                · exact ⟨u, hu, dominates_refl pos neg u⟩
              obtain ⟨k', hk', hm⟩ := ih k (Nat.lt_succ_self k) W hW'
              exact ⟨k', Nat.le_trans hk' (Nat.le_succ k), hm⟩
            · push Not at hdom
              obtain ⟨k', hk', hm⟩ := ih k (Nat.lt_succ_self k) (g :: W) ⟨f, h4, ha⟩
              exact ⟨k' + 1, Nat.succ_le_succ hk', a, haW, b, hbW, false, hgp, hgn, hdom, hm⟩
          · push Not at hgn
            have hdg : dominates pos neg g (fun _ => true) :=
              ⟨fun _ _ _ => rfl, fun m hm _ => by cases hgm : g (maskToV m); exact absurd hgm (hgn m hm); rfl⟩
            have hW' : HasMono pos neg W k := hasMono_drop_true hneg (hasMono_dom (W1 := g :: W) (fun u hu => by
              rcases List.mem_cons.1 hu with rfl | hu
              · exact ⟨_, List.mem_cons_self, hdg⟩
              · exact ⟨u, List.mem_cons_of_mem _ hu, dominates_refl pos neg u⟩) ⟨f, h4, ha⟩)
            obtain ⟨k', hk', hm⟩ := ih k (Nat.lt_succ_self k) W hW'
            exact ⟨k', Nat.le_trans hk' (Nat.le_succ k), hm⟩
        · push Not at hgp
          have hdg : dominates pos neg g (fun _ => false) :=
            ⟨fun m hm hgm => absurd hgm (hgp m hm), fun _ _ h => by contradiction⟩
          have hW' : HasMono pos neg W k := hasMono_drop_false (hasMono_dom (W1 := g :: W) (fun u hu => by
            rcases List.mem_cons.1 hu with rfl | hu
            · exact ⟨_, List.mem_cons_self, hdg⟩
            · exact ⟨u, List.mem_cons_of_mem _ hu, dominates_refl pos neg u⟩) ⟨f, h4, ha⟩)
          obtain ⟨k', hk', hm⟩ := ih k (Nat.lt_succ_self k) W hW'
          exact ⟨k', Nat.le_trans hk' (Nat.le_succ k), hm⟩
      · let g : F9 := fun x => a x || b x
        by_cases hgp : ∃ m ∈ pos, g (maskToV m) = true
        · by_cases hgn : ∃ m ∈ neg, g (maskToV m) = false
          · by_cases hdom : ∃ w ∈ W, dominates pos neg g w
            · obtain ⟨w, hwW, hdw⟩ := hdom
              have hW' : HasMono pos neg W k := by
                apply hasMono_dom (W1 := g :: W) _ ⟨f, h5, ha⟩
                intro u hu; rcases List.mem_cons.1 hu with rfl | hu
                · exact ⟨w, hwW, hdw⟩
                · exact ⟨u, hu, dominates_refl pos neg u⟩
              obtain ⟨k', hk', hm⟩ := ih k (Nat.lt_succ_self k) W hW'
              exact ⟨k', Nat.le_trans hk' (Nat.le_succ k), hm⟩
            · push Not at hdom
              obtain ⟨k', hk', hm⟩ := ih k (Nat.lt_succ_self k) (g :: W) ⟨f, h5, ha⟩
              exact ⟨k' + 1, Nat.succ_le_succ hk', a, haW, b, hbW, true, hgp, hgn, hdom, hm⟩
          · push Not at hgn
            have hdg : dominates pos neg g (fun _ => true) :=
              ⟨fun _ _ _ => rfl, fun m hm _ => by cases hgm : g (maskToV m); exact absurd hgm (hgn m hm); rfl⟩
            have hW' : HasMono pos neg W k := hasMono_drop_true hneg (hasMono_dom (W1 := g :: W) (fun u hu => by
              rcases List.mem_cons.1 hu with rfl | hu
              · exact ⟨_, List.mem_cons_self, hdg⟩
              · exact ⟨u, List.mem_cons_of_mem _ hu, dominates_refl pos neg u⟩) ⟨f, h5, ha⟩)
            obtain ⟨k', hk', hm⟩ := ih k (Nat.lt_succ_self k) W hW'
            exact ⟨k', Nat.le_trans hk' (Nat.le_succ k), hm⟩
        · push Not at hgp
          have hdg : dominates pos neg g (fun _ => false) :=
            ⟨fun m hm hgm => absurd hgm (hgp m hm), fun _ _ h => by contradiction⟩
          have hW' : HasMono pos neg W k := hasMono_drop_false (hasMono_dom (W1 := g :: W) (fun u hu => by
            rcases List.mem_cons.1 hu with rfl | hu
            · exact ⟨_, List.mem_cons_self, hdg⟩
            · exact ⟨u, List.mem_cons_of_mem _ hu, dominates_refl pos neg u⟩) ⟨f, h5, ha⟩)
          obtain ⟨k', hk', hm⟩ := ih k (Nat.lt_succ_self k) W hW'
          exact ⟨k', Nat.le_trans hk' (Nat.le_succ k), hm⟩
def kept {α : Type} (b : Bool) (x : α) (xs : List α) : List α :=
  if b then x :: xs else xs
def SMonoLive (pos neg : List Nat) : Nat → List F9 → Prop
  | 0, W => ∃ f, W = [f] ∧ agrees pos neg f
  | k + 1, W =>
      ∃ a b : F9, ∃ rest : List F9, ∃ isOr ka kb : Bool,
        W.Perm (a :: b :: rest) ∧
        let g : F9 := if isOr then (fun x => a x || b x) else (fun x => a x && b x)
        (∃ m ∈ pos, g (maskToV m) = true) ∧
        (∃ m ∈ neg, g (maskToV m) = false) ∧
        (∀ w ∈ W, ¬ dominates pos neg g w) ∧
        SMonoLive pos neg k (g :: kept ka a (kept kb b rest))
lemma sMonoLive_perm {pos neg : List Nat} {k : Nat} {W W' : List F9}
    (hp : W.Perm W') (h : SMonoLive pos neg k W) : SMonoLive pos neg k W' := by
  cases k with
  | zero =>
    obtain ⟨f, rfl, ha⟩ := h
    exact ⟨f, List.perm_singleton.1 hp.symm, ha⟩
  | succ k =>
    obtain ⟨a, b, rest, isOr, ka, kb, hpw, hgp, hgn, hdom, hrec⟩ := h
    exact ⟨a, b, rest, isOr, ka, kb, hp.symm.trans hpw, hgp, hgn,
      fun w hw => hdom w (hp.mem_iff.2 hw), hrec⟩
lemma list_extract_nodup {α : Type} [DecidableEq α] {x : α} {l : List α} (hnd : l.Nodup) (hx : x ∈ l) :
    ∃ r, l.Perm (x :: r) ∧ x ∉ r ∧ r.Nodup := by
  have hp : l.Perm (x :: l.erase x) := List.perm_cons_erase hx
  refine ⟨l.erase x, hp, ?_, hnd.erase x⟩
  exact (List.nodup_cons.1 (hp.nodup_iff.1 hnd)).1
lemma monoLive_to_sMonoLive {pos neg : List Nat} :
    ∀ k W, MonoLive pos neg k W →
      ∃ k' ≤ k, ∃ U : List F9, (∀ w ∈ U, w ∈ W) ∧ U.Nodup ∧ SMonoLive pos neg k' U := by
  classical
  intro k
  induction k with
  | zero =>
    intro W ⟨f, hf, ha⟩
    exact ⟨0, Nat.le_refl 0, [f], fun w hw => by rcases List.mem_singleton.1 hw with rfl; exact hf,
      List.nodup_singleton f, f, rfl, ha⟩
  | succ k ih =>
    intro W ⟨a, ha, b, hb, isOr, hgp, hgn, hdom, hrec⟩
    let g : F9 := if isOr then (fun x => a x || b x) else (fun x => a x && b x)
    obtain ⟨k', hk', U, hUW, hUnd, hSU⟩ := ih (g :: W) hrec
    by_cases hgU : g ∈ U
    · obtain ⟨r0, hUperm, hgr0, hr0nd⟩ := list_extract_nodup hUnd hgU
      have hr0W : ∀ w ∈ r0, w ∈ W := by
        intro w hw
        have hwU : w ∈ U := hUperm.mem_iff.2 (List.mem_cons_of_mem _ hw)
        rcases List.mem_cons.1 (hUW w hwU) with rfl | hwW
        · exact absurd hw hgr0
        · exact hwW
      have hab : a ≠ b := by
        intro heq; subst heq
        apply hdom a ha
        have hga : (if isOr then (fun x => a x || a x) else (fun x => a x && a x)) = a := by
          funext x; cases isOr <;> simp
        rw [hga]; exact dominates_refl pos neg a
      by_cases ha0 : a ∈ r0
      · obtain ⟨r1, hr0p, har1, hr1nd⟩ := list_extract_nodup hr0nd ha0
        by_cases hb1 : b ∈ r1
        · obtain ⟨r2, hr1p, hbr2, hr2nd⟩ := list_extract_nodup hr1nd hb1
          have har2 : a ∉ r2 := fun h => har1 (hr1p.mem_iff.2 (List.mem_cons_of_mem _ h))
          have hU2 : U.Perm (g :: kept true a (kept true b r2)) :=
            hUperm.trans ((hr0p.trans (hr1p.cons a)).cons g)
          refine ⟨k' + 1, Nat.succ_le_succ hk', a :: b :: r2, ?_, ?_, ?_⟩
          · intro w hw; rcases List.mem_cons.1 hw with rfl | hw
            · exact ha
            · rcases List.mem_cons.1 hw with rfl | hw
              · exact hb
              · exact hr0W w (hr0p.mem_iff.2 (List.mem_cons_of_mem _ (hr1p.mem_iff.2 (List.mem_cons_of_mem _ hw))))
          · exact List.nodup_cons.2 ⟨fun h => by rcases List.mem_cons.1 h with h | h; exact hab h; exact har2 h,
              List.nodup_cons.2 ⟨hbr2, hr2nd⟩⟩
          · exact ⟨a, b, r2, isOr, true, true, List.Perm.refl _, hgp, hgn,
              fun w hw => hdom w (by
                rcases List.mem_cons.1 hw with rfl | hw
                · exact ha
                · rcases List.mem_cons.1 hw with rfl | hw
                  · exact hb
                  · exact hr0W w (hr0p.mem_iff.2 (List.mem_cons_of_mem _ (hr1p.mem_iff.2 (List.mem_cons_of_mem _ hw))))),
              sMonoLive_perm hU2 hSU⟩
        · have hU2 : U.Perm (g :: kept true a (kept false b r1)) :=
            hUperm.trans (hr0p.cons g)
          refine ⟨k' + 1, Nat.succ_le_succ hk', a :: b :: r1, ?_, ?_, ?_⟩
          · intro w hw; rcases List.mem_cons.1 hw with rfl | hw
            · exact ha
            · rcases List.mem_cons.1 hw with rfl | hw
              · exact hb
              · exact hr0W w (hr0p.mem_iff.2 (List.mem_cons_of_mem _ hw))
          · exact List.nodup_cons.2 ⟨fun h => by rcases List.mem_cons.1 h with h | h; exact hab h; exact har1 h,
              List.nodup_cons.2 ⟨hb1, hr1nd⟩⟩
          · exact ⟨a, b, r1, isOr, true, false, List.Perm.refl _, hgp, hgn,
              fun w hw => hdom w (by
                rcases List.mem_cons.1 hw with rfl | hw
                · exact ha
                · rcases List.mem_cons.1 hw with rfl | hw
                  · exact hb
                  · exact hr0W w (hr0p.mem_iff.2 (List.mem_cons_of_mem _ hw))),
              sMonoLive_perm hU2 hSU⟩
      · by_cases hb0 : b ∈ r0
        · obtain ⟨r1, hr0p, hbr1, hr1nd⟩ := list_extract_nodup hr0nd hb0
          have har1 : a ∉ r1 := fun h => ha0 (hr0p.mem_iff.2 (List.mem_cons_of_mem _ h))
          have hU2 : U.Perm (g :: kept false a (kept true b r1)) :=
            hUperm.trans (hr0p.cons g)
          refine ⟨k' + 1, Nat.succ_le_succ hk', a :: b :: r1, ?_, ?_, ?_⟩
          · intro w hw; rcases List.mem_cons.1 hw with rfl | hw
            · exact ha
            · rcases List.mem_cons.1 hw with rfl | hw
              · exact hb
              · exact hr0W w (hr0p.mem_iff.2 (List.mem_cons_of_mem _ hw))
          · exact List.nodup_cons.2 ⟨fun h => by rcases List.mem_cons.1 h with h | h; exact hab h; exact har1 h,
              List.nodup_cons.2 ⟨hbr1, hr1nd⟩⟩
          · exact ⟨a, b, r1, isOr, false, true, List.Perm.refl _, hgp, hgn,
              fun w hw => hdom w (by
                rcases List.mem_cons.1 hw with rfl | hw
                · exact ha
                · rcases List.mem_cons.1 hw with rfl | hw
                  · exact hb
                  · exact hr0W w (hr0p.mem_iff.2 (List.mem_cons_of_mem _ hw))),
              sMonoLive_perm hU2 hSU⟩
        · have hU2 : U.Perm (g :: kept false a (kept false b r0)) := hUperm
          refine ⟨k' + 1, Nat.succ_le_succ hk', a :: b :: r0, ?_, ?_, ?_⟩
          · intro w hw; rcases List.mem_cons.1 hw with rfl | hw
            · exact ha
            · rcases List.mem_cons.1 hw with rfl | hw
              · exact hb
              · exact hr0W w hw
          · exact List.nodup_cons.2 ⟨fun h => by rcases List.mem_cons.1 h with h | h; exact hab h; exact ha0 h,
              List.nodup_cons.2 ⟨hb0, hr0nd⟩⟩
          · exact ⟨a, b, r0, isOr, false, false, List.Perm.refl _, hgp, hgn,
              fun w hw => hdom w (by
                rcases List.mem_cons.1 hw with rfl | hw
                · exact ha
                · rcases List.mem_cons.1 hw with rfl | hw
                  · exact hb
                  · exact hr0W w hw),
              sMonoLive_perm hU2 hSU⟩
    · refine ⟨k', Nat.le_trans hk' (Nat.le_succ k), U, ?_, hUnd, hSU⟩
      intro w hw
      rcases List.mem_cons.1 (hUW w hw) with rfl | hwW
      · exact absurd hw hgU
      · exact hwW
lemma sMonoLive_to_hasMono {pos neg : List Nat} :
    ∀ k W, SMonoLive pos neg k W → HasMono pos neg W k := by
  intro k
  induction k with
  | zero =>
    rintro W ⟨f, rfl, ha⟩
    exact ⟨f, Or.inl List.mem_cons_self, ha⟩
  | succ k ih =>
    intro W ⟨a, b, rest, isOr, ka, kb, hp, _, _, _, hrec⟩
    obtain ⟨f, hf, ha⟩ := ih _ hrec
    let g : F9 := if isOr then (fun x => a x || b x) else (fun x => a x && b x)
    have hsub : ∀ w ∈ g :: kept ka a (kept kb b rest), w ∈ g :: W := by
      intro w hw
      rcases List.mem_cons.1 hw with rfl | hw
      · exact List.mem_cons_self
      · apply List.mem_cons_of_mem; rw [hp.mem_iff]
        cases ka <;> cases kb <;> simp only [kept, ite_true, ite_false, Bool.false_eq_true, List.mem_cons] at hw ⊢ <;> tauto
    have haW : a ∈ W := hp.mem_iff.2 List.mem_cons_self
    have hbW : b ∈ W := hp.mem_iff.2 (List.mem_cons_of_mem _ List.mem_cons_self)
    cases isOr
    · exact ⟨f, Or.inr (Or.inr (Or.inr (Or.inl ⟨a, haW, b, hbW, monoReach_mono hsub hf⟩))), ha⟩
    · exact ⟨f, Or.inr (Or.inr (Or.inr (Or.inr ⟨a, haW, b, hbW, monoReach_mono hsub hf⟩))), ha⟩
lemma sMonoLive_covers {pos neg : List Nat} :
    ∀ k W, SMonoLive pos neg k W →
      ∀ e ∈ pos, ∀ m ∈ neg, ∃ w ∈ W, w (maskToV e) = true ∧ w (maskToV m) = false := by
  intro k
  induction k with
  | zero =>
    rintro W ⟨f, rfl, ha⟩ e he m hm
    exact ⟨f, List.mem_cons_self, ha.1 e he, ha.2 m hm⟩
  | succ k ih =>
    intro W ⟨a, b, rest, isOr, ka, kb, hp, _, _, _, hrec⟩ e he m hm
    obtain ⟨w, hw, hwe, hwm⟩ := ih _ hrec e he m hm
    rcases List.mem_cons.1 hw with rfl | hw
    · cases isOr
      · simp only [ite_false, Bool.false_eq_true, Bool.and_eq_true, Bool.and_eq_false_iff] at hwe hwm
        rcases hwm with hma | hmb
        · exact ⟨a, hp.mem_iff.2 List.mem_cons_self, hwe.1, hma⟩
        · exact ⟨b, hp.mem_iff.2 (List.mem_cons_of_mem _ List.mem_cons_self), hwe.2, hmb⟩
      · simp only [ite_true, Bool.or_eq_true, Bool.or_eq_false_iff] at hwe hwm
        rcases hwe with hea | heb
        · exact ⟨a, hp.mem_iff.2 List.mem_cons_self, hea, hwm.1⟩
        · exact ⟨b, hp.mem_iff.2 (List.mem_cons_of_mem _ List.mem_cons_self), heb, hwm.2⟩
    · refine ⟨w, hp.mem_iff.2 ?_, hwe, hwm⟩
      cases ka <;> cases kb <;> simp only [kept, ite_true, ite_false, Bool.false_eq_true, List.mem_cons] at hw ⊢ <;> tauto
def SubValid (pos neg : List Nat) (v : Fin 9) (pos_v neg_v : List Nat) : Prop :=
  pos_v ≠ [] ∧ neg_v ≠ [] ∧
  (∀ e ∈ pos_v, e ∈ pos ∧ e.testBit v.1 = false) ∧
  (∀ m ∈ neg_v, m.testBit v.1 = false ∧ ∃ m' ∈ neg, (m &&& m') = m)
lemma agrees_projV {pos neg pos_v neg_v : List Nat} {v : Fin 9} {f : F9}
    (hsv : SubValid pos neg v pos_v neg_v) (hmono : IsMono f) (ha : agrees pos neg f) :
    agrees pos_v neg_v (projV v f) := by
  obtain ⟨_, _, hpos, hneg⟩ := hsv
  refine ⟨fun e he => ?_, fun m hm => ?_⟩
  · obtain ⟨hep, hv0⟩ := hpos e he
    have heq : (fun i => if i = v then false else maskToV e i) = maskToV e := by
      funext i; by_cases hi : i = v
      · subst hi; simp [maskToV, hv0]
      · simp [hi]
    show f (fun i => if i = v then false else maskToV e i) = true
    rw [heq]; exact ha.1 e hep
  · obtain ⟨hv0, m', hm', hland⟩ := hneg m hm
    have heq : (fun i => if i = v then false else maskToV m i) = maskToV m := by
      funext i; by_cases hi : i = v
      · subst hi; simp [maskToV, hv0]
      · simp [hi]
    show f (fun i => if i = v then false else maskToV m i) = false
    rw [heq]
    cases hfm : f (maskToV m)
    · rfl
    · have hle : ∀ i, maskToV m i = true → maskToV m' i = true := by
        intro i hi
        have htb := congrArg (fun x => x.testBit i.1) hland
        rw [Nat.testBit_and] at htb
        have hi' : m.testBit i.1 = true := hi
        rw [hi'] at htb; simpa [maskToV] using htb.symm
      have h2 := hmono _ _ hle hfm
      rw [ha.2 m' hm'] at h2; contradiction
lemma hasMono_step_projV {pos_v neg_v : List Nat} {v : Fin 9} {W W' : List F9}
    {a b : F9} {isOr : Bool} {k : Nat}
    (ha : a ∈ W) (hb : b ∈ W)
    (hsub : ∀ w ∈ W', w ∈ (if isOr then (fun x => a x || b x) else (fun x => a x && b x)) :: W)
    (h : HasMono pos_v neg_v (W'.map (projV v)) k) :
    HasMono pos_v neg_v (W.map (projV v)) (k + 1) := by
  obtain ⟨f, hf, hag⟩ := h
  let g : F9 := if isOr then (fun x => a x || b x) else (fun x => a x && b x)
  have hf1 : MonoReach k (projV v g :: W.map (projV v)) f := by
    apply monoReach_mono _ hf
    intro u hu; rw [List.mem_map] at hu; obtain ⟨w, hw, rfl⟩ := hu
    rcases List.mem_cons.1 (hsub w hw) with rfl | hwW
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (List.mem_map_of_mem hwW)
  cases isOr
  · exact ⟨f, Or.inr (Or.inr (Or.inr (Or.inl ⟨projV v a, List.mem_map_of_mem ha, projV v b, List.mem_map_of_mem hb, hf1⟩))), hag⟩
  · exact ⟨f, Or.inr (Or.inr (Or.inr (Or.inr ⟨projV v a, List.mem_map_of_mem ha, projV v b, List.mem_map_of_mem hb, hf1⟩))), hag⟩
lemma hasMono_zero_step_projV {pos_v neg_v : List Nat} {v : Fin 9} {W W' : List F9}
    {a b : F9} {isOr : Bool} {k : Nat}
    (hb : b ∈ W) (hz : projV v a = fun _ => false)
    (hsub : ∀ w ∈ W', w ∈ (if isOr then (fun x => a x || b x) else (fun x => a x && b x)) :: W)
    (h : HasMono pos_v neg_v (W'.map (projV v)) k) :
    HasMono pos_v neg_v (W.map (projV v)) k := by
  let g : F9 := if isOr then (fun x => a x || b x) else (fun x => a x && b x)
  cases isOr
  · have hgp : projV v g = fun _ => false := by
      funext x; change (projV v a x && projV v b x) = false; rw [hz]; rfl
    apply hasMono_drop_false
    apply hasMono_mono_W _ h
    intro u hu; rw [List.mem_map] at hu; obtain ⟨w, hw, rfl⟩ := hu
    rcases List.mem_cons.1 (hsub w hw) with rfl | hwW
    · rw [hgp]; exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (List.mem_map_of_mem hwW)
  · have hgp : projV v g = projV v b := by
      funext x; change (projV v a x || projV v b x) = projV v b x; rw [hz]; rfl
    apply hasMono_mono_W _ h
    intro u hu; rw [List.mem_map] at hu; obtain ⟨w, hw, rfl⟩ := hu
    rcases List.mem_cons.1 (hsub w hw) with rfl | hwW
    · rw [hgp]; exact List.mem_map_of_mem hb
    · exact List.mem_map_of_mem hwW
lemma sMonoLive_projV_hasMono {pos neg pos_v neg_v : List Nat} {v : Fin 9}
    (hsv : SubValid pos neg v pos_v neg_v) {k : Nat} {W : List F9}
    (hWmono : ∀ w ∈ W, IsMono w) (h : SMonoLive pos neg k W) :
    HasMono pos_v neg_v (W.map (projV v)) k := by
  obtain ⟨f, hf, hag⟩ := sMonoLive_to_hasMono k W h
  exact ⟨projV v f, monoReach_projV v hf, agrees_projV hsv (monoReach_isMono hWmono hf) hag⟩
lemma isMono_step {W : List F9} {a b : F9} {rest : List F9} {isOr ka kb : Bool}
    (hWmono : ∀ w ∈ W, IsMono w) (hp : W.Perm (a :: b :: rest)) :
    ∀ w ∈ (if isOr then (fun x => a x || b x) else (fun x => a x && b x)) :: kept ka a (kept kb b rest), IsMono w := by
  intro w hw
  have ha := hWmono a (hp.mem_iff.2 List.mem_cons_self)
  have hb := hWmono b (hp.mem_iff.2 (List.mem_cons_of_mem _ List.mem_cons_self))
  rcases List.mem_cons.1 hw with rfl | hw
  · cases isOr
    · intro x y hxy h1; simp only [Bool.false_eq_true, ite_false, Bool.and_eq_true] at h1 ⊢; exact ⟨ha x y hxy h1.1, hb x y hxy h1.2⟩
    · intro x y hxy h1; simp only [ite_true, Bool.or_eq_true] at h1 ⊢; exact h1.elim (fun h => Or.inl (ha x y hxy h)) (fun h => Or.inr (hb x y hxy h))
  · apply hWmono w; rw [hp.mem_iff]
    cases ka <;> cases kb <;> simp only [kept, ite_true, ite_false, Bool.false_eq_true, List.mem_cons] at hw ⊢ <;> tauto
lemma one_zero_wire_save_one {pos neg pos_v neg_v : List Nat} {v : Fin 9}
    (hsv : SubValid pos neg v pos_v neg_v) :
    ∀ k W, (∀ w ∈ W, IsMono w) → SMonoLive pos neg k W →
      ∀ z ∈ W, projV v z = (fun _ => false) →
        1 ≤ k ∧ HasMono pos_v neg_v (W.map (projV v)) (k - 1) := by
  intro k
  induction k with
  | zero =>
    rintro W hWmono ⟨f, rfl, hag⟩ z hz hzp
    rcases List.mem_singleton.1 hz with rfl
    have hag' := agrees_projV hsv (hWmono z List.mem_cons_self) hag
    rw [hzp] at hag'
    cases hpn : pos_v with
    | nil => exact absurd hpn hsv.1
    | cons e _ =>
      have := hag'.1 e (by rw [hpn]; exact List.mem_cons_self)
      contradiction
  | succ k ih =>
    intro W hWmono ⟨a, b, rest, isOr, ka, kb, hp, _, _, _, hrec⟩ z hz hzp
    have hsub : ∀ w ∈ (if isOr then (fun x => a x || b x) else (fun x => a x && b x)) :: kept ka a (kept kb b rest),
        w ∈ (if isOr then (fun x => a x || b x) else (fun x => a x && b x)) :: W := by
      intro w hw; rcases List.mem_cons.1 hw with rfl | hw
      · exact List.mem_cons_self
      · apply List.mem_cons_of_mem; rw [hp.mem_iff]
        cases ka <;> cases kb <;> simp only [kept, ite_true, ite_false, Bool.false_eq_true, List.mem_cons] at hw ⊢ <;> tauto
    have haW : a ∈ W := hp.mem_iff.2 List.mem_cons_self
    have hbW : b ∈ W := hp.mem_iff.2 (List.mem_cons_of_mem _ List.mem_cons_self)
    have hW'mono := isMono_step hWmono hp (isOr := isOr) (ka := ka) (kb := kb)
    have hz' : z ∈ a :: b :: rest := hp.mem_iff.1 hz
    rcases List.mem_cons.1 hz' with rfl | hz'
    · refine ⟨Nat.succ_pos _, ?_⟩
      exact hasMono_zero_step_projV hbW hzp hsub (sMonoLive_projV_hasMono hsv hW'mono hrec)
    · rcases List.mem_cons.1 hz' with rfl | hzr
      · refine ⟨Nat.succ_pos _, ?_⟩
        have hsub' : ∀ w ∈ (if isOr then (fun x => a x || z x) else (fun x => a x && z x)) :: kept ka a (kept kb z rest),
            w ∈ (if isOr then (fun x => z x || a x) else (fun x => z x && a x)) :: W := by
          have heq : (if isOr then (fun x => a x || z x) else (fun x => a x && z x)) =
                     (if isOr then (fun x => z x || a x) else (fun x => z x && a x)) := by
            funext x; cases isOr <;> simp [Bool.and_comm, Bool.or_comm]
          rw [← heq]; exact hsub
        exact hasMono_zero_step_projV haW hzp hsub' (sMonoLive_projV_hasMono hsv hW'mono hrec)
      · have hzW' : z ∈ (if isOr then (fun x => a x || b x) else (fun x => a x && b x)) :: kept ka a (kept kb b rest) := by
          apply List.mem_cons_of_mem
          cases ka <;> cases kb <;> simp only [kept, ite_true, ite_false, Bool.false_eq_true, List.mem_cons] <;> tauto
        obtain ⟨hk1, hhm⟩ := ih _ hW'mono hrec z hzW' hzp
        refine ⟨Nat.succ_pos _, ?_⟩
        have hstep := hasMono_step_projV haW hbW hsub hhm
        have heq : k - 1 + 1 = k := by omega
        rwa [heq] at hstep
lemma two_zero_wires_save_two {pos neg pos_v neg_v : List Nat} {v : Fin 9}
    (hsv : SubValid pos neg v pos_v neg_v) :
    ∀ k W, (∀ w ∈ W, IsMono w) → SMonoLive pos neg k W →
      ∀ z1 z2 r, W.Perm (z1 :: z2 :: r) →
        projV v z1 = (fun _ => false) → projV v z2 = (fun _ => false) →
          2 ≤ k ∧ HasMono pos_v neg_v (W.map (projV v)) (k - 2) := by
  classical
  intro k
  induction k with
  | zero =>
    rintro W _ ⟨f, rfl, _⟩ z1 z2 r hp _ _
    have hlen := hp.length_eq; simp at hlen
  | succ k ih =>
    intro W hWmono ⟨a, b, rest, isOr, ka, kb, hp, _, _, _, hrec⟩ z1 z2 r hpz hz1 hz2
    have hsub : ∀ w ∈ (if isOr then (fun x => a x || b x) else (fun x => a x && b x)) :: kept ka a (kept kb b rest),
        w ∈ (if isOr then (fun x => a x || b x) else (fun x => a x && b x)) :: W := by
      intro w hw; rcases List.mem_cons.1 hw with rfl | hw
      · exact List.mem_cons_self
      · apply List.mem_cons_of_mem; rw [hp.mem_iff]
        cases ka <;> cases kb <;> simp only [kept, ite_true, ite_false, Bool.false_eq_true, List.mem_cons] at hw ⊢ <;> tauto
    have haW : a ∈ W := hp.mem_iff.2 List.mem_cons_self
    have hbW : b ∈ W := hp.mem_iff.2 (List.mem_cons_of_mem _ List.mem_cons_self)
    have hW'mono := isMono_step hWmono hp (isOr := isOr) (ka := ka) (kb := kb)
    by_cases haz : projV v a = (fun _ => false)
    · by_cases hbz : projV v b = (fun _ => false)
      · have hgz : projV v (if isOr then (fun x => a x || b x) else (fun x => a x && b x)) = fun _ => false := by
          funext x; cases isOr
          · change (projV v a x && projV v b x) = false; rw [haz]; rfl
          · change (projV v a x || projV v b x) = false; rw [haz, hbz]; rfl
        obtain ⟨hk1, hhm⟩ := one_zero_wire_save_one hsv k _ hW'mono hrec _ List.mem_cons_self hgz
        refine ⟨by omega, ?_⟩
        have h0 := hasMono_zero_step_projV hbW haz hsub hhm
        have heq : k - 1 = k + 1 - 2 := by omega
        rwa [heq] at h0
      · have hcnt : (a :: b :: rest).countP (fun w => decide (projV v w = fun _ => false)) ≥ 2 := by
          have hp2 : (a :: b :: rest).Perm (z1 :: z2 :: r) := hp.symm.trans hpz
          rw [hp2.countP_eq]
          simp [List.countP_cons, hz1, hz2]
        simp only [List.countP_cons, haz, hbz, decide_true, decide_false, Bool.false_eq_true, ite_true, ite_false] at hcnt
        have hpos_r : 0 < rest.countP (fun w => decide (projV v w = fun _ => false)) := by omega
        obtain ⟨z3, hz3r, hz3p⟩ := List.countP_pos_iff.1 hpos_r
        have hz3z : projV v z3 = fun _ => false := of_decide_eq_true hz3p
        have hz3W' : z3 ∈ (if isOr then (fun x => a x || b x) else (fun x => a x && b x)) :: kept ka a (kept kb b rest) := by
          apply List.mem_cons_of_mem
          cases ka <;> cases kb <;> simp only [kept, ite_true, ite_false, Bool.false_eq_true, List.mem_cons] <;> tauto
        obtain ⟨hk1, hhm⟩ := one_zero_wire_save_one hsv k _ hW'mono hrec z3 hz3W' hz3z
        refine ⟨by omega, ?_⟩
        have h0 := hasMono_zero_step_projV hbW haz hsub hhm
        have heq : k - 1 = k + 1 - 2 := by omega
        rwa [heq] at h0
    · by_cases hbz : projV v b = (fun _ => false)
      · have hcnt : (a :: b :: rest).countP (fun w => decide (projV v w = fun _ => false)) ≥ 2 := by
          have hp2 : (a :: b :: rest).Perm (z1 :: z2 :: r) := hp.symm.trans hpz
          rw [hp2.countP_eq]
          simp [List.countP_cons, hz1, hz2]
        simp only [List.countP_cons, haz, hbz, decide_true, decide_false, Bool.false_eq_true, ite_true, ite_false] at hcnt
        have hpos_r : 0 < rest.countP (fun w => decide (projV v w = fun _ => false)) := by omega
        obtain ⟨z3, hz3r, hz3p⟩ := List.countP_pos_iff.1 hpos_r
        have hz3z : projV v z3 = fun _ => false := of_decide_eq_true hz3p
        have hz3W' : z3 ∈ (if isOr then (fun x => a x || b x) else (fun x => a x && b x)) :: kept ka a (kept kb b rest) := by
          apply List.mem_cons_of_mem
          cases ka <;> cases kb <;> simp only [kept, ite_true, ite_false, Bool.false_eq_true, List.mem_cons] <;> tauto
        obtain ⟨hk1, hhm⟩ := one_zero_wire_save_one hsv k _ hW'mono hrec z3 hz3W' hz3z
        refine ⟨by omega, ?_⟩
        have hsub' : ∀ w ∈ (if isOr then (fun x => a x || b x) else (fun x => a x && b x)) :: kept ka a (kept kb b rest),
            w ∈ (if isOr then (fun x => b x || a x) else (fun x => b x && a x)) :: W := by
          have heq : (if isOr then (fun x => a x || b x) else (fun x => a x && b x)) =
                     (if isOr then (fun x => b x || a x) else (fun x => b x && a x)) := by
            funext x; cases isOr <;> simp [Bool.and_comm, Bool.or_comm]
          rw [← heq]; exact hsub
        have h0 := hasMono_zero_step_projV haW hbz hsub' hhm
        have heq : k - 1 = k + 1 - 2 := by omega
        rwa [heq] at h0
      · have hp2 : (a :: b :: rest).Perm (z1 :: z2 :: r) := hp.symm.trans hpz
        have hz1r : z1 ∈ rest := by
          have hm : z1 ∈ a :: b :: rest := hp2.mem_iff.2 List.mem_cons_self
          rcases List.mem_cons.1 hm with rfl | hm
          · exact absurd hz1 haz
          · rcases List.mem_cons.1 hm with rfl | hm
            · exact absurd hz1 hbz
            · exact hm
        have hpr1 : (a :: b :: rest.erase z1).Perm (z2 :: r) := by
          have h1 : (z1 :: a :: b :: rest.erase z1).Perm (a :: b :: rest) :=
            (List.Perm.swap _ _ _).trans (((List.Perm.swap _ _ _).cons a).trans
              (((List.perm_cons_erase hz1r).symm.cons b).cons a))
          exact (h1.trans hp2).cons_inv
        have hz2r : z2 ∈ rest.erase z1 := by
          have hm : z2 ∈ a :: b :: rest.erase z1 := hpr1.mem_iff.2 List.mem_cons_self
          rcases List.mem_cons.1 hm with rfl | hm
          · exact absurd hz2 haz
          · rcases List.mem_cons.1 hm with rfl | hm
            · exact absurd hz2 hbz
            · exact hm
        have hrest_p : rest.Perm (z1 :: z2 :: (rest.erase z1).erase z2) :=
          (List.perm_cons_erase hz1r).trans ((List.perm_cons_erase hz2r).cons z1)
        let r' := (rest.erase z1).erase z2
        let g := if isOr then (fun x => a x || b x) else (fun x => a x && b x)
        have hW'p : (g :: kept ka a (kept kb b rest)).Perm (z1 :: z2 :: g :: kept ka a (kept kb b r')) := by
          have hkept : ∀ (c : Bool) (x : F9) (l1 l2 : List F9), l1.Perm l2 → (kept c x l1).Perm (kept c x l2) := by
            intro c x l1 l2 h; cases c <;> simp only [kept, ite_true, ite_false, Bool.false_eq_true]
            · exact h
            · exact h.cons x
          have h1 : (g :: kept ka a (kept kb b rest)).Perm (g :: kept ka a (kept kb b (z1 :: z2 :: r'))) :=
            (hkept ka a _ _ (hkept kb b _ _ hrest_p)).cons g
          apply h1.trans
          cases ka <;> cases kb <;> simp only [kept, ite_true, ite_false, Bool.false_eq_true]
          · exact (List.Perm.swap _ _ _).trans ((List.Perm.swap _ _ _).cons z1)
          · exact (((List.Perm.swap _ _ _).cons g).trans (List.Perm.swap _ _ _)).trans
              (((((List.Perm.swap _ _ _).cons g).trans (List.Perm.swap _ _ _))).cons z1)
          · exact (((List.Perm.swap _ _ _).cons g).trans (List.Perm.swap _ _ _)).trans
              (((((List.Perm.swap _ _ _).cons g).trans (List.Perm.swap _ _ _))).cons z1)
          · have hs1 : (g :: a :: b :: z1 :: z2 :: r').Perm (z1 :: g :: a :: b :: z2 :: r') :=
              (((List.Perm.swap _ _ _).cons a).cons g).trans
                (((List.Perm.swap _ _ _).cons g).trans (List.Perm.swap _ _ _))
            have hs2 : (g :: a :: b :: z2 :: r').Perm (z2 :: g :: a :: b :: r') :=
              (((List.Perm.swap _ _ _).cons a).cons g).trans
                (((List.Perm.swap _ _ _).cons g).trans (List.Perm.swap _ _ _))
            exact hs1.trans (hs2.cons z1)
        obtain ⟨hk2, hhm⟩ := ih _ hW'mono hrec z1 z2 _ hW'p hz1 hz2
        refine ⟨by omega, ?_⟩
        have hstep := hasMono_step_projV haW hbW hsub hhm
        have heq : k - 2 + 1 = k + 1 - 2 := by omega
        rwa [heq] at hstep
def encPos (pos : List Nat) (N : Nat) (f : F9) : Nat :=
  (List.range pos.length).foldl (fun acc i =>
    if f (maskToV (pos.getD i 0)) then
      acc ||| (((1 <<< N) - 1) <<< (i * N))
    else acc) 0
def encNeg (P : Nat) (neg : List Nat) (f : F9) : Nat :=
  let rowBits := (List.range neg.length).foldl (fun acc j =>
    if f (maskToV (neg.getD j 0)) then acc ||| (1 <<< j) else acc) 0
  (List.range P).foldl (fun acc i => acc ||| (rowBits <<< (i * neg.length))) 0
lemma testBit_one_shl_sub_one (N k : Nat) :
    ((1 <<< N) - 1).testBit k = decide (k < N) := by
  have h : (1 <<< N) = 2 ^ N := by simp [Nat.shiftLeft_eq]
  rw [h, Nat.testBit_two_pow_sub_one]
lemma encPos_testBit_aux (pos : List Nat) (N : Nat) (f : F9) (n acc : Nat) (i j : Nat) (hj : j < N) :
    ((List.range n).foldl (fun a r =>
      if f (maskToV (pos.getD r 0)) then a ||| (((1 <<< N) - 1) <<< (r * N)) else a) acc).testBit (i * N + j) =
    (acc.testBit (i * N + j) || (decide (i < n) && f (maskToV (pos.getD i 0)))) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    by_cases hf : f (maskToV (pos.getD n 0)) = true
    · simp only [hf, ite_true, Nat.testBit_or, Nat.testBit_shiftLeft, testBit_one_shl_sub_one, ih]
      by_cases hin : i = n
      · rw [hin]
        have h1 : n * N ≤ n * N + j := Nat.le_add_right _ _
        have h2 : n * N + j - n * N < N := by omega
        simp only [ge_iff_le, decide_eq_true h1, decide_eq_true h2, hf,
          decide_eq_true (Nat.lt_succ_self n), decide_eq_false (Nat.lt_irrefl n),
          Bool.true_and, Bool.false_and, Bool.or_false, Bool.or_true]
      · have hdiff : ¬ (n * N ≤ i * N + j ∧ i * N + j - n * N < N) := by
          intro ⟨h1, h2⟩
          rcases Nat.lt_or_gt.1 hin with hlt | hgt
          · have : (i + 1) * N ≤ n * N := Nat.mul_le_mul_right N hlt
            rw [Nat.add_mul, Nat.one_mul] at this; omega
          · have : (n + 1) * N ≤ i * N := Nat.mul_le_mul_right N hgt
            rw [Nat.add_mul, Nat.one_mul] at this; omega
        have hlt_eq : decide (i < n + 1) = decide (i < n) := decide_eq_decide.2 (by omega)
        have hfalse : (decide (n * N ≤ i * N + j) && decide (i * N + j - n * N < N)) = false := by
          by_cases h1 : n * N ≤ i * N + j
          · have h2 : ¬ (i * N + j - n * N < N) := fun hh => hdiff ⟨h1, hh⟩
            simp [h1, h2]
          · simp [h1]
        rw [hfalse, Bool.or_false, hlt_eq]
    · have hff : f (maskToV (pos.getD n 0)) = false := Bool.eq_false_iff.2 hf
      simp only [hff, Bool.false_eq_true, ite_false, ih]
      by_cases hin : i = n
      · subst hin; simp only [hff, Nat.lt_succ_self, Nat.lt_irrefl, decide_true, decide_false, Bool.and_false]
      · rw [decide_eq_decide.2 (show i < n + 1 ↔ i < n by omega)]
lemma encPos_testBit (pos : List Nat) (N : Nat) (f : F9) (i j : Nat) (hj : j < N) :
    (encPos pos N f).testBit (i * N + j) = (decide (i < pos.length) && f (maskToV (pos.getD i 0))) := by
  unfold encPos
  rw [encPos_testBit_aux pos N f pos.length 0 i j hj]
  simp
lemma encPos_lt (pos : List Nat) (N : Nat) (f : F9) (hN : 0 < N) :
    encPos pos N f < 2 ^ (pos.length * N) := by
  apply Nat.lt_pow_two_of_testBit
  intro k hk
  have hdiv : k = (k / N) * N + k % N := by rw [Nat.mul_comm]; exact (Nat.div_add_mod k N).symm
  have hmod : k % N < N := Nat.mod_lt k hN
  have hge : pos.length ≤ k / N := by
    by_contra hlt; push Not at hlt
    have : (k / N + 1) * N ≤ pos.length * N := Nat.mul_le_mul_right N hlt
    rw [Nat.add_mul, Nat.one_mul] at this; omega
  rw [hdiv, encPos_testBit pos N f (k / N) (k % N) hmod]
  simp [show ¬ k / N < pos.length by omega]
lemma encNeg_row_testBit (neg : List Nat) (f : F9) (n acc j : Nat) :
    ((List.range n).foldl (fun a r => if f (maskToV (neg.getD r 0)) then a ||| (1 <<< r) else a) acc).testBit j =
    (acc.testBit j || (decide (j < n) && f (maskToV (neg.getD j 0)))) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    by_cases hf : f (maskToV (neg.getD n 0)) = true
    · simp only [hf, ite_true, Nat.testBit_or, Nat.testBit_shiftLeft, testBit_one_eq, ih]
      by_cases hjn : j = n
      · subst hjn; simp only [ge_iff_le, hf, Nat.le_refl, Nat.sub_self, Nat.lt_succ_self, Nat.lt_irrefl, decide_true, decide_false, Bool.true_and, Bool.false_and, Bool.or_false, Bool.or_true]
      · have h1 : (decide (n ≤ j) && decide (j - n = 0)) = false := by
          by_cases hle : n ≤ j
          · simp [hle, show j - n ≠ 0 by omega]
          · simp [hle]
        rw [h1, Bool.or_false, decide_eq_decide.2 (show j < n + 1 ↔ j < n by omega)]
    · have hff : f (maskToV (neg.getD n 0)) = false := Bool.eq_false_iff.2 hf
      simp only [hff, Bool.false_eq_true, ite_false, ih]
      by_cases hjn : j = n
      · subst hjn; simp only [hff, Nat.lt_succ_self, Nat.lt_irrefl, decide_true, decide_false, Bool.and_false]
      · rw [decide_eq_decide.2 (show j < n + 1 ↔ j < n by omega)]
lemma encNeg_broadcast_testBit (rb N : Nat) (hrb : ∀ k, N ≤ k → rb.testBit k = false)
    (n acc i j : Nat) (hj : j < N) :
    ((List.range n).foldl (fun a r => a ||| (rb <<< (r * N))) acc).testBit (i * N + j) =
    (acc.testBit (i * N + j) || (decide (i < n) && rb.testBit j)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    simp only [Nat.testBit_or, Nat.testBit_shiftLeft, ih]
    by_cases hin : i = n
    · rw [hin]
      have h1 : n * N ≤ n * N + j := Nat.le_add_right _ _
      have h2 : n * N + j - n * N = j := by omega
      simp [ge_iff_le, h1, h2]
    · have hfalse : (decide (n * N ≤ i * N + j) && rb.testBit (i * N + j - n * N)) = false := by
        by_cases hle : n * N ≤ i * N + j
        · have hgt : n < i := by
            by_contra hle'; push Not at hle'
            have hlt : i < n := Nat.lt_of_le_of_ne hle' hin
            have : (i + 1) * N ≤ n * N := Nat.mul_le_mul_right N hlt
            rw [Nat.add_mul, Nat.one_mul] at this; omega
          have hgeN : N ≤ i * N + j - n * N := by
            have : (n + 1) * N ≤ i * N := Nat.mul_le_mul_right N hgt
            rw [Nat.add_mul, Nat.one_mul] at this; omega
          simp [hle, hrb _ hgeN]
        · simp [hle]
      rw [hfalse, Bool.or_false, decide_eq_decide.2 (show i < n + 1 ↔ i < n by omega)]
lemma encNeg_testBit (P : Nat) (neg : List Nat) (f : F9) (i j : Nat) (hj : j < neg.length) :
    (encNeg P neg f).testBit (i * neg.length + j) = (decide (i < P) && f (maskToV (neg.getD j 0))) := by
  unfold encNeg
  set rb := (List.range neg.length).foldl (fun acc j => if f (maskToV (neg.getD j 0)) then acc ||| (1 <<< j) else acc) 0
  have hrb : ∀ k, neg.length ≤ k → rb.testBit k = false := by
    intro k hk; rw [encNeg_row_testBit]; simp [show ¬ k < neg.length by omega]
  rw [encNeg_broadcast_testBit rb neg.length hrb P 0 i j hj]
  have hrbj : rb.testBit j = f (maskToV (neg.getD j 0)) := by
    rw [encNeg_row_testBit]; simp [hj]
  simp [hrbj]
lemma encNeg_lt (P : Nat) (neg : List Nat) (f : F9) (hN : 0 < neg.length) :
    encNeg P neg f < 2 ^ (P * neg.length) := by
  apply Nat.lt_pow_two_of_testBit
  intro k hk
  set N := neg.length
  have hdiv : k = (k / N) * N + k % N := by rw [Nat.mul_comm]; exact (Nat.div_add_mod k N).symm
  have hmod : k % N < N := Nat.mod_lt k hN
  have hge : P ≤ k / N := by
    by_contra hlt; push Not at hlt
    have : (k / N + 1) * N ≤ P * N := Nat.mul_le_mul_right N hlt
    rw [Nat.add_mul, Nat.one_mul] at this; omega
  rw [hdiv, encNeg_testBit P neg f (k / N) (k % N) hmod]
  simp [show ¬ k / N < P by omega]
lemma encPos_and (pos : List Nat) (N : Nat) (hN : 0 < N) (a b : F9) :
    encPos pos N (fun x => a x && b x) = (encPos pos N a &&& encPos pos N b) := by
  apply Nat.eq_of_testBit_eq; intro k
  have hdiv : k = (k / N) * N + k % N := by rw [Nat.mul_comm]; exact (Nat.div_add_mod k N).symm
  have hmod : k % N < N := Nat.mod_lt k hN
  rw [hdiv, Nat.testBit_and, encPos_testBit _ _ _ _ _ hmod, encPos_testBit _ _ _ _ _ hmod, encPos_testBit _ _ _ _ _ hmod]
  cases decide (k / N < pos.length) <;> simp
lemma encPos_or (pos : List Nat) (N : Nat) (hN : 0 < N) (a b : F9) :
    encPos pos N (fun x => a x || b x) = (encPos pos N a ||| encPos pos N b) := by
  apply Nat.eq_of_testBit_eq; intro k
  have hdiv : k = (k / N) * N + k % N := by rw [Nat.mul_comm]; exact (Nat.div_add_mod k N).symm
  have hmod : k % N < N := Nat.mod_lt k hN
  rw [hdiv, Nat.testBit_or, encPos_testBit _ _ _ _ _ hmod, encPos_testBit _ _ _ _ _ hmod, encPos_testBit _ _ _ _ _ hmod]
  cases decide (k / N < pos.length) <;> simp
lemma encNeg_and (P : Nat) (neg : List Nat) (hN : 0 < neg.length) (a b : F9) :
    encNeg P neg (fun x => a x && b x) = (encNeg P neg a &&& encNeg P neg b) := by
  apply Nat.eq_of_testBit_eq; intro k
  set N := neg.length
  have hdiv : k = (k / N) * N + k % N := by rw [Nat.mul_comm]; exact (Nat.div_add_mod k N).symm
  have hmod : k % N < N := Nat.mod_lt k hN
  rw [hdiv, Nat.testBit_and, encNeg_testBit _ _ _ _ _ hmod, encNeg_testBit _ _ _ _ _ hmod, encNeg_testBit _ _ _ _ _ hmod]
  cases decide (k / N < P) <;> simp
lemma encNeg_or (P : Nat) (neg : List Nat) (hN : 0 < neg.length) (a b : F9) :
    encNeg P neg (fun x => a x || b x) = (encNeg P neg a ||| encNeg P neg b) := by
  apply Nat.eq_of_testBit_eq; intro k
  set N := neg.length
  have hdiv : k = (k / N) * N + k % N := by rw [Nat.mul_comm]; exact (Nat.div_add_mod k N).symm
  have hmod : k % N < N := Nat.mod_lt k hN
  rw [hdiv, Nat.testBit_or, encNeg_testBit _ _ _ _ _ hmod, encNeg_testBit _ _ _ _ _ hmod, encNeg_testBit _ _ _ _ _ hmod]
  cases decide (k / N < P) <;> simp
def RowColConst (P N : Nat) (p n : Nat) : Prop :=
  p < 2 ^ (P * N) ∧ n < 2 ^ (P * N) ∧
  (∀ i < P, ∀ j < N, p.testBit (i * N + j) = p.testBit (i * N)) ∧
  (∀ i < P, ∀ j < N, n.testBit (i * N + j) = n.testBit j)
lemma enc_rowColConst (pos neg : List Nat) (hP : 0 < pos.length) (hN : 0 < neg.length) (f : F9) :
    RowColConst pos.length neg.length (encPos pos neg.length f) (encNeg pos.length neg f) := by
  refine ⟨encPos_lt pos neg.length f hN, encNeg_lt pos.length neg f hN, ?_, ?_⟩
  · intro i hi j hj
    have h0 := encPos_testBit pos neg.length f i 0 hN
    have hj' := encPos_testBit pos neg.length f i j hj
    simp only [Nat.add_zero] at h0; rw [h0, hj']
  · intro i hi j hj
    have h0 := encNeg_testBit pos.length neg f 0 j hj
    have hi' := encNeg_testBit pos.length neg f i j hj
    simp only [Nat.zero_mul, Nat.zero_add, hP, decide_true, Bool.true_and] at h0
    simp only [hi, decide_true, Bool.true_and] at hi'
    rw [h0, hi']
lemma rowColConst_and {P N p1 n1 p2 n2 : Nat}
    (h1 : RowColConst P N p1 n1) (h2 : RowColConst P N p2 n2) :
    RowColConst P N (p1 &&& p2) (n1 &&& n2) := by
  refine ⟨Nat.lt_of_le_of_lt Nat.and_le_left h1.1, Nat.lt_of_le_of_lt Nat.and_le_left h1.2.1, ?_, ?_⟩
  · intro i hi j hj; simp [Nat.testBit_and, h1.2.2.1 i hi j hj, h2.2.2.1 i hi j hj]
  · intro i hi j hj; simp [Nat.testBit_and, h1.2.2.2 i hi j hj, h2.2.2.2 i hi j hj]
lemma rowColConst_or {P N p1 n1 p2 n2 : Nat}
    (h1 : RowColConst P N p1 n1) (h2 : RowColConst P N p2 n2) :
    RowColConst P N (p1 ||| p2) (n1 ||| n2) := by
  refine ⟨Nat.or_lt_two_pow h1.1 h2.1, Nat.or_lt_two_pow h1.2.1 h2.2.1, ?_, ?_⟩
  · intro i hi j hj; simp [Nat.testBit_or, h1.2.2.1 i hi j hj, h2.2.2.1 i hi j hj]
  · intro i hi j hj; simp [Nat.testBit_or, h1.2.2.2 i hi j hj, h2.2.2.2 i hi j hj]
def NatTRestricted (top : Nat) : Nat → List (Nat × Nat × Nat) → Prop
  | 0, ws => ∃ t, ws = [(top, 0, t)]
  | k + 1, ws =>
      ∃ pa na ta pb nb tb : Nat, ∃ rest : List (Nat × Nat × Nat), ∃ isOr ka kb : Bool,
        ws.Perm ((pa, na, ta) :: (pb, nb, tb) :: rest) ∧
        (isOr = true ∨ (ta ≠ 2 ∧ tb ≠ 2)) ∧
        (ka = false ∨ (if isOr then ta ≠ 2 else ta = 0)) ∧
        (kb = false ∨ (if isOr then tb ≠ 2 else tb = 0)) ∧
        let gp := if isOr then (pa ||| pb) else (pa &&& pb)
        let gn := if isOr then (na ||| nb) else (na &&& nb)
        gp ≠ 0 ∧ gn ≠ top ∧
        (∀ w ∈ ws, ¬ ((gp &&& w.1) = gp ∧ (w.2.1 &&& gn) = w.2.1)) ∧
        let tg := if !isOr && (Nat.beq ta 1 || Nat.beq tb 1) then 2 else 0
        let ta' := if isOr && Nat.beq ta 1 then 2 else ta
        let tb' := if isOr && Nat.beq tb 1 then 2 else tb
        NatTRestricted top k ((gp, gn, tg) :: kept ka (pa, na, ta') (kept kb (pb, nb, tb') rest))
lemma natTRestricted_perm {top k : Nat} {ws zs : List (Nat × Nat × Nat)}
    (hp : ws.Perm zs) (h : NatTRestricted top k ws) : NatTRestricted top k zs := by
  cases k with
  | zero =>
    obtain ⟨t, rfl⟩ := h
    exact ⟨t, List.perm_singleton.1 hp.symm⟩
  | succ k =>
    obtain ⟨pa, na, ta, pb, nb, tb, rest, isOr, ka, kb, hpw, h1, h2, h3, hgp, hgn, hdom, hrec⟩ := h
    exact ⟨pa, na, ta, pb, nb, tb, rest, isOr, ka, kb, hp.symm.trans hpw, h1, h2, h3, hgp, hgn,
      fun w hw => hdom w (hp.mem_iff.2 hw), hrec⟩
lemma natTRestricted_len {top : Nat} :
    ∀ k ws, NatTRestricted top k ws → ws.length ≤ k + 1 := by
  intro k
  induction k with
  | zero => rintro ws ⟨t, rfl⟩; simp
  | succ k ih =>
    intro ws ⟨pa, na, ta, pb, nb, tb, rest, isOr, ka, kb, hp, _, _, _, _, _, _, hrec⟩
    have hl := hp.length_eq
    have hr := ih _ hrec
    cases ka <;> cases kb <;> simp only [kept, ite_true, ite_false, Bool.false_eq_true, List.length_cons] at hr hl ⊢ <;> omega
lemma perm_map_exists {α β : Type} (f : α → β) {l : List α} {m : List β}
    (h : (l.map f).Perm m) : ∃ l', l.Perm l' ∧ l'.map f = m := by
  suffices ∀ m1 m2, m1.Perm m2 → ∀ l : List α, l.map f = m1 → ∃ l', l.Perm l' ∧ l'.map f = m2 from
    this (l.map f) m h l rfl
  intro m1 m2 hp
  induction hp with
  | nil =>
    intro l hl; cases l with
    | nil => exact ⟨[], .nil, rfl⟩
    | cons _ _ => simp at hl
  | cons x _ ih =>
    intro l hl; cases l with
    | nil => simp at hl
    | cons a t =>
      simp only [List.map_cons, List.cons.injEq] at hl
      obtain ⟨t', ht'p, ht'm⟩ := ih t hl.2
      exact ⟨a :: t', ht'p.cons a, by simp [hl.1, ht'm]⟩
  | swap x y t =>
    intro l hl; cases l with
    | nil => simp at hl
    | cons a l1 =>
      cases l1 with
      | nil => simp at hl
      | cons b t' =>
        simp only [List.map_cons, List.cons.injEq] at hl
        exact ⟨b :: a :: t', List.Perm.swap _ _ _, by simp [hl.1, hl.2.1, hl.2.2]⟩
  | trans _ _ ih1 ih2 =>
    intro l hl
    obtain ⟨l1, h1p, h1m⟩ := ih1 l hl
    obtain ⟨l2, h2p, h2m⟩ := ih2 l1 h1m
    exact ⟨l2, h1p.trans h2p, h2m⟩
def TagOk (pos neg : List Nat) (W : List F9) (k : Nat) (w : F9) : Nat → Prop
  | 0 => True
  | 1 => ∃ v pos_v neg_v, SubValid pos neg v pos_v neg_v ∧ projV v w = (fun _ => false) ∧
      ∀ m, m + 3 ≤ k → ¬ HasMono pos_v neg_v (W.map (projV v)) m
  | 2 => ∃ v pos_v neg_v, SubValid pos neg v pos_v neg_v ∧ projV v w = (fun _ => false) ∧
      ∀ m, m + 2 ≤ k → ¬ HasMono pos_v neg_v (W.map (projV v)) m
  | _ => False
lemma sMonoLive_to_nat {pos neg : List Nat} (hP : 0 < pos.length) (hN : 0 < neg.length) :
    ∀ k (W : List (F9 × Nat)),
      (∀ wt ∈ W, IsMono wt.1) →
      (∀ wt ∈ W, TagOk pos neg (W.map Prod.fst) k wt.1 wt.2) →
      SMonoLive pos neg k (W.map Prod.fst) →
      NatTRestricted (2 ^ (pos.length * neg.length) - 1) k
        (W.map fun wt => (encPos pos neg.length wt.1, encNeg pos.length neg wt.1, wt.2)) := by
  set P := pos.length
  set N := neg.length
  set top := 2 ^ (P * N) - 1
  intro k
  induction k with
  | zero =>
    intro W _ _ ⟨f, hmap, hag⟩
    cases W with
    | nil => simp at hmap
    | cons wt rest =>
      cases rest with
      | cons _ _ => simp at hmap
      | nil =>
        simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hmap
        subst hmap
        refine ⟨wt.2, ?_⟩
        simp only [List.map_cons, List.map_nil, List.cons.injEq, Prod.mk.injEq, and_true]
        refine ⟨?_, ?_⟩
        · apply Nat.eq_of_testBit_eq; intro idx
          have hdiv : idx = (idx / N) * N + idx % N := by rw [Nat.mul_comm]; exact (Nat.div_add_mod idx N).symm
          have hmod : idx % N < N := Nat.mod_lt idx hN
          rw [hdiv, encPos_testBit _ _ _ _ _ hmod, Nat.testBit_two_pow_sub_one]
          by_cases hi : idx / N < P
          · have hlt : (idx / N) * N + idx % N < P * N := by
              have : (idx / N + 1) * N ≤ P * N := Nat.mul_le_mul_right N hi
              rw [Nat.add_mul, Nat.one_mul] at this; omega
            have hmem : pos.getD (idx / N) 0 ∈ pos := by
              have h1 : pos.getD (idx / N) 0 = pos[idx / N]'hi := by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
              rw [h1]; exact List.getElem_mem hi
            have ht : wt.1 (maskToV (pos.getD (idx / N) 0)) = true := hag.1 _ hmem
            have hd1 : decide (idx / N < pos.length) = true := decide_eq_true hi
            have hd2 : decide ((idx / N) * N + idx % N < P * N) = true := decide_eq_true hlt
            rw [hd1, hd2, ht]; rfl
          · have hge : ¬ ((idx / N) * N + idx % N < P * N) := by
              have : P * N ≤ (idx / N) * N := Nat.mul_le_mul_right N (Nat.le_of_not_lt hi)
              omega
            have hd1 : decide (idx / N < pos.length) = false := decide_eq_false hi
            have hd2 : decide ((idx / N) * N + idx % N < P * N) = false := decide_eq_false hge
            rw [hd1, hd2]; rfl
        · apply Nat.eq_of_testBit_eq; intro idx
          have hdiv : idx = (idx / N) * N + idx % N := by rw [Nat.mul_comm]; exact (Nat.div_add_mod idx N).symm
          have hmod : idx % N < N := Nat.mod_lt idx hN
          rw [hdiv, encNeg_testBit _ _ _ _ _ hmod, Nat.zero_testBit]
          have hmem : neg.getD (idx % N) 0 ∈ neg := by
            have h1 : neg.getD (idx % N) 0 = neg[idx % N]'hmod := by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hmod]
            rw [h1]; exact List.getElem_mem hmod
          have hf : wt.1 (maskToV (neg.getD (idx % N) 0)) = false := hag.2 _ hmem
          rw [hf, Bool.and_false]
  | succ k ih =>
    intro W hWmono hTags ⟨a, b, rest, isOr, ka, kb, hp, hgp, hgn, hdom, hrec⟩
    obtain ⟨wa, wb, wrest, hWperm, hwa1, hwb1, hrest_eq⟩ :
        ∃ wa wb wrest, W.Perm (wa :: wb :: wrest) ∧ wa.1 = a ∧ wb.1 = b ∧ wrest.map Prod.fst = rest := by
      obtain ⟨l', hl'p, hl'm⟩ := perm_map_exists Prod.fst hp
      cases l' with
      | nil => simp at hl'm
      | cons wa l1 =>
        cases l1 with
        | nil => simp at hl'm
        | cons wb wrest =>
          simp only [List.map_cons, List.cons.injEq] at hl'm
          exact ⟨wa, wb, wrest, hl'p, hl'm.1, hl'm.2.1, hl'm.2.2⟩
    subst hwa1; subst hwb1
    let pa := encPos pos N wa.1; let na := encNeg P neg wa.1; let ta := wa.2
    let pb := encPos pos N wb.1; let nb := encNeg P neg wb.1; let tb := wb.2
    let g : F9 := if isOr then (fun x => wa.1 x || wb.1 x) else (fun x => wa.1 x && wb.1 x)
    let gp := if isOr then (pa ||| pb) else (pa &&& pb)
    let gn := if isOr then (na ||| nb) else (na &&& nb)
    let tg := if !isOr && (Nat.beq ta 1 || Nat.beq tb 1) then 2 else 0
    let ta' := if isOr && Nat.beq ta 1 then 2 else ta
    let tb' := if isOr && Nat.beq tb 1 then 2 else tb
    have hgp_eq : gp = encPos pos N g := by
      cases isOr <;> simp only [gp, g, pa, pb, ite_true, ite_false, Bool.false_eq_true]
      · exact (encPos_and pos N hN wa.1 wb.1).symm
      · exact (encPos_or pos N hN wa.1 wb.1).symm
    have hgn_eq : gn = encNeg P neg g := by
      cases isOr <;> simp only [gn, g, na, nb, ite_true, ite_false, Bool.false_eq_true]
      · exact (encNeg_and P neg hN wa.1 wb.1).symm
      · exact (encNeg_or P neg hN wa.1 wb.1).symm
    have hwaW : wa ∈ W := hWperm.mem_iff.2 List.mem_cons_self
    have hwbW : wb ∈ W := hWperm.mem_iff.2 (List.mem_cons_of_mem _ List.mem_cons_self)
    have hWmonoF : ∀ w ∈ W.map Prod.fst, IsMono w := by
      intro w hw; rw [List.mem_map] at hw; obtain ⟨wt, hwt, rfl⟩ := hw; exact hWmono wt hwt
    have hW'mono_w : ∀ w ∈ g :: kept ka wa.1 (kept kb wb.1 (wrest.map Prod.fst)), IsMono w := by
      rw [hrest_eq]; exact isMono_step hWmonoF hp (isOr := isOr) (ka := ka) (kb := kb)
    have hrec_w : SMonoLive pos neg k (g :: kept ka wa.1 (kept kb wb.1 (wrest.map Prod.fst))) := by
      rwa [hrest_eq]
    have hsubW : ∀ w ∈ g :: kept ka wa.1 (kept kb wb.1 (wrest.map Prod.fst)), w ∈ g :: W.map Prod.fst := by
      intro w hw; rcases List.mem_cons.1 hw with rfl | hw
      · exact List.mem_cons_self
      · apply List.mem_cons_of_mem; rw [hp.mem_iff, ← hrest_eq]
        cases ka <;> cases kb <;> simp only [kept, ite_true, ite_false, Bool.false_eq_true, List.mem_cons] at hw ⊢ <;> tauto
    have haMem : wa.1 ∈ W.map Prod.fst := List.mem_map_of_mem hwaW
    have hbMem : wb.1 ∈ W.map Prod.fst := List.mem_map_of_mem hwbW
    have hsubW_sym : ∀ w ∈ g :: kept ka wa.1 (kept kb wb.1 (wrest.map Prod.fst)),
        w ∈ (if isOr then (fun x => wb.1 x || wa.1 x) else (fun x => wb.1 x && wa.1 x)) :: W.map Prod.fst := by
      have heq : g = (if isOr then (fun x => wb.1 x || wa.1 x) else (fun x => wb.1 x && wa.1 x)) := by
        funext x; cases isOr <;> simp [g, Bool.and_comm, Bool.or_comm]
      rw [← heq]; exact hsubW
    have hta_le : ta = 0 ∨ ta = 1 ∨ ta = 2 := by
      have h := hTags wa hwaW
      rcases hta : wa.2 with _ | n1
      · left; exact hta
      · rcases n1 with _ | n2
        · right; left; exact hta
        · rcases n2 with _ | _
          · right; right; exact hta
          · rw [hta] at h; exact False.elim h
    have htb_le : tb = 0 ∨ tb = 1 ∨ tb = 2 := by
      have h := hTags wb hwbW
      rcases htb : wb.2 with _ | n1
      · left; exact htb
      · rcases n1 with _ | n2
        · right; left; exact htb
        · rcases n2 with _ | _
          · right; right; exact htb
          · rw [htb] at h; exact False.elim h
    have h_and_not2 : isOr = true ∨ (ta ≠ 2 ∧ tb ≠ 2) := by
      cases isOr
      · right; constructor
        · intro hta2
          have hta : TagOk pos neg (W.map Prod.fst) (k + 1) wa.1 ta := hTags wa hwaW; rw [hta2] at hta
          obtain ⟨v, pv, nv, hsv, hzv, hno⟩ := hta
          have hgz : projV v g = fun _ => false := by
            funext x; change (projV v wa.1 x && projV v wb.1 x) = false; rw [hzv]; rfl
          obtain ⟨hk1, hhm⟩ := one_zero_wire_save_one hsv k _ hW'mono_w hrec_w g List.mem_cons_self hgz
          exact hno (k - 1) (by omega) (hasMono_zero_step_projV hbMem hzv hsubW hhm)
        · intro htb2
          have htb : TagOk pos neg (W.map Prod.fst) (k + 1) wb.1 tb := hTags wb hwbW; rw [htb2] at htb
          obtain ⟨v, pv, nv, hsv, hzv, hno⟩ := htb
          have hgz : projV v g = fun _ => false := by
            funext x; change (projV v wa.1 x && projV v wb.1 x) = false; rw [hzv]; simp
          obtain ⟨hk1, hhm⟩ := one_zero_wire_save_one hsv k _ hW'mono_w hrec_w g List.mem_cons_self hgz
          exact hno (k - 1) (by omega) (hasMono_zero_step_projV haMem hzv hsubW_sym hhm)
      · left; rfl
    have h_ka_ok : ka = false ∨ (if isOr then ta ≠ 2 else ta = 0) := by
      cases ka
      · left; rfl
      · right; cases isOr
        · simp only [Bool.false_eq_true, ite_false]
          rcases hta_le with h0 | h1 | h2
          · exact h0
          · exfalso
            have hta : TagOk pos neg (W.map Prod.fst) (k + 1) wa.1 ta := hTags wa hwaW; rw [h1] at hta
            obtain ⟨v, pv, nv, hsv, hzv, hno⟩ := hta
            have hgz : projV v g = fun _ => false := by
              funext x; change (projV v wa.1 x && projV v wb.1 x) = false; rw [hzv]; rfl
            obtain ⟨hk2, hhm⟩ := two_zero_wires_save_two hsv k _ hW'mono_w hrec_w g wa.1 _ (List.Perm.refl _) hgz hzv
            exact hno (k - 2) (by omega) (hasMono_zero_step_projV hbMem hzv hsubW hhm)
          · exact absurd h2 (h_and_not2.resolve_left (by decide)).1
        · simp only [ite_true]
          intro hta2
          have hta : TagOk pos neg (W.map Prod.fst) (k + 1) wa.1 ta := hTags wa hwaW; rw [hta2] at hta
          obtain ⟨v, pv, nv, hsv, hzv, hno⟩ := hta
          have ha_in : wa.1 ∈ g :: kept true wa.1 (kept kb wb.1 (wrest.map Prod.fst)) :=
            List.mem_cons_of_mem _ List.mem_cons_self
          obtain ⟨hk1, hhm⟩ := one_zero_wire_save_one hsv k _ hW'mono_w hrec_w wa.1 ha_in hzv
          exact hno (k - 1) (by omega) (hasMono_zero_step_projV hbMem hzv hsubW hhm)
    have h_kb_ok : kb = false ∨ (if isOr then tb ≠ 2 else tb = 0) := by
      cases kb
      · left; rfl
      · right; cases isOr
        · simp only [Bool.false_eq_true, ite_false]
          rcases htb_le with h0 | h1 | h2
          · exact h0
          · exfalso
            have htb : TagOk pos neg (W.map Prod.fst) (k + 1) wb.1 tb := hTags wb hwbW; rw [h1] at htb
            obtain ⟨v, pv, nv, hsv, hzv, hno⟩ := htb
            have hgz : projV v g = fun _ => false := by
              funext x; change (projV v wa.1 x && projV v wb.1 x) = false; rw [hzv]; simp
            have hperm2 : (g :: kept ka wa.1 (wb.1 :: wrest.map Prod.fst)).Perm (g :: wb.1 :: kept ka wa.1 (wrest.map Prod.fst)) := by
              cases ka <;> simp only [kept, ite_true, ite_false, Bool.false_eq_true]
              · exact List.Perm.refl _
              · exact (List.Perm.swap _ _ _).cons g
            obtain ⟨hk2, hhm⟩ := two_zero_wires_save_two hsv k _ hW'mono_w hrec_w g wb.1 _ hperm2 hgz hzv
            exact hno (k - 2) (by omega) (hasMono_zero_step_projV haMem hzv hsubW_sym hhm)
          · exact absurd h2 (h_and_not2.resolve_left (by decide)).2
        · simp only [ite_true]
          intro htb2
          have htb : TagOk pos neg (W.map Prod.fst) (k + 1) wb.1 tb := hTags wb hwbW; rw [htb2] at htb
          obtain ⟨v, pv, nv, hsv, hzv, hno⟩ := htb
          have hb_in : wb.1 ∈ g :: kept ka wa.1 (kept true wb.1 (wrest.map Prod.fst)) := by
            apply List.mem_cons_of_mem; cases ka <;> simp [kept]
          obtain ⟨hk1, hhm⟩ := one_zero_wire_save_one hsv k _ hW'mono_w hrec_w wb.1 hb_in hzv
          exact hno (k - 1) (by omega) (hasMono_zero_step_projV haMem hzv hsubW_sym hhm)
    have hgp_ne : gp ≠ 0 := by
      intro h0; rw [hgp_eq] at h0
      obtain ⟨m, hm, hgm⟩ := hgp
      obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hm
      have htb := congrArg (fun x => x.testBit (i * N + 0)) h0
      rw [encPos_testBit pos N g i 0 hN, Nat.zero_testBit] at htb
      have hget : pos.getD i 0 = pos[i]'hi := by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
      have hgm' : g (maskToV pos[i]) = true := hgm
      rw [hget, hgm', decide_eq_true hi] at htb; contradiction
    have hgn_ne : gn ≠ top := by
      intro ht; rw [hgn_eq] at ht
      obtain ⟨m, hm, hgm⟩ := hgn
      obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 hm
      have htb := congrArg (fun x => x.testBit (0 * N + j)) ht
      rw [encNeg_testBit P neg g 0 j hj, Nat.testBit_two_pow_sub_one] at htb
      have hget : neg.getD j 0 = neg[j]'hj := by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
      have hlt : 0 * N + j < P * N := by
        have : 1 * N ≤ P * N := Nat.mul_le_mul_right N hP
        omega
      have hgm' : g (maskToV neg[j]) = false := hgm
      rw [hget, hgm', decide_eq_true hlt] at htb; simp at htb
    have hdom_nat : ∀ w ∈ W.map (fun wt => (encPos pos N wt.1, encNeg P neg wt.1, wt.2)),
        ¬ ((gp &&& w.1) = gp ∧ (w.2.1 &&& gn) = w.2.1) := by
      intro w hw ⟨hdp, hdn⟩
      rw [List.mem_map] at hw; obtain ⟨wt, hwt, rfl⟩ := hw
      apply hdom wt.1 (List.mem_map_of_mem hwt)
      refine ⟨fun m hm hgm => ?_, fun m hm hwm => ?_⟩
      · obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hm
        have htb := congrArg (fun x => x.testBit (i * N + 0)) hdp
        rw [hgp_eq, Nat.testBit_and, encPos_testBit pos N g i 0 hN, encPos_testBit pos N wt.1 i 0 hN] at htb
        have hget : pos.getD i 0 = pos[i]'hi := by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
        have hgm' : g (maskToV pos[i]) = true := hgm
        rw [hget, decide_eq_true hi, hgm'] at htb; simpa using htb
      · obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 hm
        have htb := congrArg (fun x => x.testBit (0 * N + j)) hdn
        rw [hgn_eq, Nat.testBit_and, encNeg_testBit P neg wt.1 0 j hj, encNeg_testBit P neg g 0 j hj] at htb
        have hget : neg.getD j 0 = neg[j]'hj := by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
        rw [hget, decide_eq_true hP, hwm] at htb; simpa using htb
    let W' : List (F9 × Nat) := (g, tg) :: kept ka (wa.1, ta') (kept kb (wb.1, tb') wrest)
    have hW'_fst : W'.map Prod.fst = g :: kept ka wa.1 (kept kb wb.1 (wrest.map Prod.fst)) := by
      cases ka <;> cases kb <;> simp [W', kept]
    have hW'_mono : ∀ wt ∈ W', IsMono wt.1 := by
      intro wt hwt
      exact hW'mono_w wt.1 (by rw [← hW'_fst]; exact List.mem_map_of_mem hwt)
    have hW'_tags : ∀ wt ∈ W', TagOk pos neg (W'.map Prod.fst) k wt.1 wt.2 := by
      intro wt hwt
      rw [hW'_fst]
      rcases List.mem_cons.1 hwt with rfl | hwt
      · -- New gate (g, tg)
        change TagOk pos neg _ k g tg
        dsimp only [tg]
        cases isOr
        · by_cases h1 : (Nat.beq ta 1 || Nat.beq tb 1) = true
          · rw [Bool.not_false, Bool.true_and, h1]; dsimp only [ite_true, TagOk]
            simp only [Bool.or_eq_true, Nat.beq_eq] at h1
            rcases h1 with hta1 | htb1
            · have hta : TagOk pos neg (W.map Prod.fst) (k + 1) wa.1 ta := hTags wa hwaW; rw [hta1] at hta
              obtain ⟨v, pv, nv, hsv, hzv, hno⟩ := hta
              refine ⟨v, pv, nv, hsv, ?_, fun m hm hhm => hno m (by omega) (hasMono_zero_step_projV hbMem hzv hsubW hhm)⟩
              funext x; change (projV v wa.1 x && projV v wb.1 x) = false; rw [hzv]; rfl
            · have htb : TagOk pos neg (W.map Prod.fst) (k + 1) wb.1 tb := hTags wb hwbW; rw [htb1] at htb
              obtain ⟨v, pv, nv, hsv, hzv, hno⟩ := htb
              refine ⟨v, pv, nv, hsv, ?_, fun m hm hhm => hno m (by omega) (hasMono_zero_step_projV haMem hzv hsubW_sym hhm)⟩
              funext x; change (projV v wa.1 x && projV v wb.1 x) = false; rw [hzv]; simp
          · have hf : (Nat.beq ta 1 || Nat.beq tb 1) = false := Bool.eq_false_iff.2 h1
            simp [hf, TagOk]
        · simp [TagOk]
      · -- Kept a, kept b, or element of wrest
        have hstep_tag : ∀ u : F9 × Nat, u ∈ W → TagOk pos neg (W.map Prod.fst) (k + 1) u.1 u.2 →
            TagOk pos neg (g :: kept ka wa.1 (kept kb wb.1 (wrest.map Prod.fst))) k u.1 u.2 := by
          intro u _ hu
          rcases hu2 : u.2 with _ | n1
          · trivial
          · rcases n1 with _ | n2
            · rw [hu2] at hu; obtain ⟨v, pv, nv, hsv, hzv, hno⟩ := hu
              exact ⟨v, pv, nv, hsv, hzv, fun m hm hhm => hno (m + 1) (by omega) (hasMono_step_projV haMem hbMem hsubW hhm)⟩
            · rcases n2 with _ | _
              · rw [hu2] at hu; obtain ⟨v, pv, nv, hsv, hzv, hno⟩ := hu
                exact ⟨v, pv, nv, hsv, hzv, fun m hm hhm => hno (m + 1) (by omega) (hasMono_step_projV haMem hbMem hsubW hhm)⟩
              · rw [hu2] at hu; exact False.elim hu
        have hmem_case : (ka = true ∧ wt = (wa.1, ta')) ∨ (kb = true ∧ wt = (wb.1, tb')) ∨ wt ∈ wrest := by
          cases ka <;> cases kb <;> simp only [kept, ite_true, ite_false, Bool.false_eq_true, List.mem_cons] at hwt
          · exact Or.inr (Or.inr hwt)
          · rcases hwt with rfl | hwt; exact Or.inr (Or.inl ⟨rfl, rfl⟩); exact Or.inr (Or.inr hwt)
          · rcases hwt with rfl | hwt; exact Or.inl ⟨rfl, rfl⟩; exact Or.inr (Or.inr hwt)
          · rcases hwt with rfl | rfl | hwt
            · exact Or.inl ⟨rfl, rfl⟩
            · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
            · exact Or.inr (Or.inr hwt)
        rcases hmem_case with ⟨hka, rfl⟩ | ⟨hkb, rfl⟩ | hwrest
        · dsimp only [ta']
          by_cases h1 : (isOr && Nat.beq ta 1) = true
          · rw [h1]; dsimp only [ite_true, TagOk]
            simp only [Bool.and_eq_true, Nat.beq_eq] at h1
            have hta : TagOk pos neg (W.map Prod.fst) (k + 1) wa.1 ta := hTags wa hwaW; rw [h1.2] at hta
            obtain ⟨v, pv, nv, hsv, hzv, hno⟩ := hta
            exact ⟨v, pv, nv, hsv, hzv, fun m hm hhm => hno m (by omega) (hasMono_zero_step_projV hbMem hzv hsubW hhm)⟩
          · have hf : (isOr && Nat.beq ta 1) = false := Bool.eq_false_iff.2 h1
            simp only [hf, ite_false, Bool.false_eq_true]
            exact hstep_tag wa hwaW (hTags wa hwaW)
        · dsimp only [tb']
          by_cases h1 : (isOr && Nat.beq tb 1) = true
          · rw [h1]; dsimp only [ite_true, TagOk]
            simp only [Bool.and_eq_true, Nat.beq_eq] at h1
            have htb : TagOk pos neg (W.map Prod.fst) (k + 1) wb.1 tb := hTags wb hwbW; rw [h1.2] at htb
            obtain ⟨v, pv, nv, hsv, hzv, hno⟩ := htb
            exact ⟨v, pv, nv, hsv, hzv, fun m hm hhm => hno m (by omega) (hasMono_zero_step_projV haMem hzv hsubW_sym hhm)⟩
          · have hf : (isOr && Nat.beq tb 1) = false := Bool.eq_false_iff.2 h1
            simp only [hf, ite_false, Bool.false_eq_true]
            exact hstep_tag wb hwbW (hTags wb hwbW)
        · have hwW : wt ∈ W := hWperm.mem_iff.2 (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hwrest))
          exact hstep_tag wt hwW (hTags wt hwW)
    have hrec_nat := ih W' hW'_mono hW'_tags (by rwa [hW'_fst])
    have hW'_enc : (W'.map fun wt => (encPos pos N wt.1, encNeg P neg wt.1, wt.2)) =
        (gp, gn, tg) :: kept ka (pa, na, ta') (kept kb (pb, nb, tb')
          (wrest.map fun wt => (encPos pos N wt.1, encNeg P neg wt.1, wt.2))) := by
      cases ka <;> cases kb <;> simp [W', kept, hgp_eq, hgn_eq, pa, na, pb, nb]
    rw [hW'_enc] at hrec_nat
    exact ⟨pa, na, ta, pb, nb, tb, wrest.map fun wt => (encPos pos N wt.1, encNeg P neg wt.1, wt.2),
      isOr, ka, kb, hWperm.map _, h_and_not2, h_ka_ok, h_kb_ok, hgp_ne, hgn_ne, hdom_nat, hrec_nat⟩
def sepsOr (top : Nat) : List (Nat × Nat × Nat) → Nat
  | [] => 0
  | (p, n, _) :: rest => (p &&& (n ^^^ top)) ||| sepsOr top rest
lemma sepsOr_perm (top : Nat) {l1 l2 : List (Nat × Nat × Nat)} (hp : l1.Perm l2) :
    sepsOr top l1 = sepsOr top l2 := by
  induction hp with
  | nil => rfl
  | cons a _ ih => rcases a with ⟨p, n, t⟩; simp [sepsOr, ih]
  | swap a b _ =>
    rcases a with ⟨p1, n1, t1⟩; rcases b with ⟨p2, n2, t2⟩
    apply Nat.eq_of_testBit_eq; intro k
    simp [sepsOr, Nat.testBit_or, Bool.or_left_comm]
  | trans _ _ ih1 ih2 => exact ih1.trans ih2
lemma sep_and_le (top pa na pb nb : Nat) (k : Nat) (ht : top.testBit k = true) :
    (((pa &&& pb) &&& ((na &&& nb) ^^^ top)).testBit k = true) →
    ((pa &&& (na ^^^ top)).testBit k = true ∨ (pb &&& (nb ^^^ top)).testBit k = true) := by
  simp only [Nat.testBit_and, Nat.testBit_xor, ht]
  cases pa.testBit k <;> cases pb.testBit k <;> cases na.testBit k <;> cases nb.testBit k <;> simp
lemma sep_or_le (top pa na pb nb : Nat) (k : Nat) (ht : top.testBit k = true) :
    (((pa ||| pb) &&& ((na ||| nb) ^^^ top)).testBit k = true) →
    ((pa &&& (na ^^^ top)).testBit k = true ∨ (pb &&& (nb ^^^ top)).testBit k = true) := by
  simp only [Nat.testBit_and, Nat.testBit_or, Nat.testBit_xor, ht]
  cases pa.testBit k <;> cases pb.testBit k <;> cases na.testBit k <;> cases nb.testBit k <;> simp
lemma natTRestricted_sepsOr {M : Nat} :
    ∀ k ws, (∀ w ∈ ws, w.1 < 2 ^ M) → NatTRestricted (2 ^ M - 1) k ws →
      sepsOr (2 ^ M - 1) ws = 2 ^ M - 1 := by
  set top := 2 ^ M - 1
  intro k
  induction k with
  | zero =>
    rintro ws _ ⟨t, rfl⟩
    apply Nat.eq_of_testBit_eq; intro idx
    simp [sepsOr, Nat.testBit_or, Nat.testBit_and, Nat.testBit_xor]
  | succ k ih =>
    intro ws hlt ⟨pa, na, ta, pb, nb, tb, rest, isOr, ka, kb, hp, _, _, _, _, _, _, hrec⟩
    have hlt_a : pa < 2 ^ M := hlt (pa, na, ta) (hp.mem_iff.2 List.mem_cons_self)
    have hlt_b : pb < 2 ^ M := hlt (pb, nb, tb) (hp.mem_iff.2 (List.mem_cons_of_mem _ List.mem_cons_self))
    have hlt' : ∀ w ∈ (if isOr then (pa ||| pb) else (pa &&& pb),
        if isOr then (na ||| nb) else (na &&& nb),
        if !isOr && (Nat.beq ta 1 || Nat.beq tb 1) then 2 else 0) ::
        kept ka (pa, na, if isOr && Nat.beq ta 1 then 2 else ta)
          (kept kb (pb, nb, if isOr && Nat.beq tb 1 then 2 else tb) rest), w.1 < 2 ^ M := by
      intro w hw; rcases List.mem_cons.1 hw with rfl | hw
      · cases isOr
        · exact Nat.lt_of_le_of_lt Nat.and_le_left hlt_a
        · exact Nat.or_lt_two_pow hlt_a hlt_b
      · cases ka <;> cases kb <;> simp only [kept, ite_true, ite_false, Bool.false_eq_true, List.mem_cons] at hw
        · exact hlt w (hp.mem_iff.2 (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hw)))
        · rcases hw with rfl | hw; exact hlt_b; exact hlt w (hp.mem_iff.2 (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hw)))
        · rcases hw with rfl | hw; exact hlt_a; exact hlt w (hp.mem_iff.2 (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hw)))
        · rcases hw with rfl | rfl | hw
          · exact hlt_a
          · exact hlt_b
          · exact hlt w (hp.mem_iff.2 (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hw)))
    have hcov := ih _ hlt' hrec
    rw [sepsOr_perm top hp]
    apply Nat.eq_of_testBit_eq; intro idx
    have hle_top : ∀ l : List (Nat × Nat × Nat), (∀ w ∈ l, w.1 < 2 ^ M) → (sepsOr top l).testBit idx = true → top.testBit idx = true := by
      intro l hl
      induction l with
      | nil => simp [sepsOr]
      | cons w t ihl =>
        rcases w with ⟨p, n, tg⟩
        simp only [sepsOr, Nat.testBit_or, Nat.testBit_and, Nat.testBit_xor, Bool.or_eq_true, Bool.and_eq_true]
        rintro (⟨hp', _⟩ | hr)
        · have hplt : p < 2 ^ M := hl (p, n, tg) List.mem_cons_self
          have hidx : idx < M := by
            by_contra hge; push Not at hge
            have h0 := Nat.testBit_eq_false_of_lt (Nat.lt_of_lt_of_le hplt (Nat.pow_le_pow_right (by omega) hge))
            rw [hp'] at h0; contradiction
          simp [top, Nat.testBit_two_pow_sub_one, hidx]
        · exact ihl (fun w' hw' => hl w' (List.mem_cons_of_mem _ hw')) hr
    cases hti : top.testBit idx
    · cases hs : (sepsOr top ((pa, na, ta) :: (pb, nb, tb) :: rest)).testBit idx
      · rfl
      · have := hle_top _ (fun w hw => hlt w (hp.mem_iff.2 hw)) hs; rw [hti] at this; contradiction
    · have hcov_i : (sepsOr top ((if isOr then (pa ||| pb) else (pa &&& pb),
          if isOr then (na ||| nb) else (na &&& nb),
          if !isOr && (Nat.beq ta 1 || Nat.beq tb 1) then 2 else 0) ::
          kept ka (pa, na, if isOr && Nat.beq ta 1 then 2 else ta)
            (kept kb (pb, nb, if isOr && Nat.beq tb 1 then 2 else tb) rest))).testBit idx = true := by
        rw [hcov]; exact hti
      simp only [sepsOr, Nat.testBit_or, Bool.or_eq_true] at hcov_i ⊢
      rcases hcov_i with hgate | htail
      · cases isOr
        · simp only [Bool.false_eq_true, ite_false] at hgate
          rcases sep_and_le top pa na pb nb idx hti hgate with ha | hb
          · exact Or.inl ha
          · exact Or.inr (Or.inl hb)
        · simp only [ite_true] at hgate
          rcases sep_or_le top pa na pb nb idx hti hgate with ha | hb
          · exact Or.inl ha
          · exact Or.inr (Or.inl hb)
      · cases ka <;> cases kb <;>
          simp only [kept, ite_true, ite_false, Bool.false_eq_true, sepsOr, Nat.testBit_or, Bool.or_eq_true] at htail <;>
          tauto
def vf (a b c d e f : Bool) : Nat :=
  let x := b.toNat + c.toNat
  let y := (!e).toNat + (!f).toNat
  if a then (if d then y else max x (max y (x + y - 1)))
  else (if d then 0 else x)
lemma vf_and : ∀ a b c d e f g h i j l m : Bool,
    vf (a && g) (b && h) (c && i) (d && j) (e && l) (f && m) ≤
      vf a b c d e f + vf g h i j l m := by decide +kernel
lemma vf_or : ∀ a b c d e f g h i j l m : Bool,
    vf (a || g) (b || h) (c || i) (d || j) (e || l) (f || m) ≤
      vf a b c d e f + vf g h i j l m := by decide +kernel
lemma list_sum_perm {l1 l2 : List Nat} (hp : l1.Perm l2) : l1.sum = l2.sum := by
  induction hp with
  | nil => rfl
  | cons _ _ ih => simp [ih]
  | swap _ _ _ => simp; omega
  | trans _ _ ih1 ih2 => exact ih1.trans ih2
lemma natTRestricted_tight_subadd {top : Nat} (v : Nat × Nat → Nat)
    (hand : ∀ p1 n1 p2 n2, v (p1 &&& p2, n1 &&& n2) ≤ v (p1, n1) + v (p2, n2))
    (hor : ∀ p1 n1 p2 n2, v (p1 ||| p2, n1 ||| n2) ≤ v (p1, n1) + v (p2, n2)) :
    ∀ k ws, NatTRestricted top k ws → ws.length = k + 1 →
      v (top, 0) ≤ (ws.map fun w => v (w.1, w.2.1)).sum := by
  intro k
  induction k with
  | zero => rintro ws ⟨t, rfl⟩ _; simp
  | succ k ih =>
    intro ws ⟨pa, na, ta, pb, nb, tb, rest, isOr, ka, kb, hp, _, _, _, _, _, _, hrec⟩ hlen
    have hrl := natTRestricted_len k _ hrec
    have hpl := hp.length_eq
    have hka : ka = false := by cases ka <;> cases kb <;> simp [kept] at hrl hpl hlen ⊢ <;> omega
    have hkb : kb = false := by cases ka <;> cases kb <;> simp [kept] at hrl hpl hlen ⊢ <;> omega
    subst hka; subst hkb
    simp only [kept, Bool.false_eq_true, ite_false] at hrec
    have hlen' : ((if isOr then pa ||| pb else pa &&& pb,
        if isOr then na ||| nb else na &&& nb,
        if !isOr && (Nat.beq ta 1 || Nat.beq tb 1) then 2 else 0) :: rest).length = k + 1 := by
      simp at hpl hlen ⊢; omega
    have ih' := ih _ hrec hlen'
    rw [list_sum_perm (hp.map (fun w => v (w.1, w.2.1)))]
    simp only [List.map_cons, List.sum_cons] at ih' ⊢
    cases isOr
    · simp only [Bool.false_eq_true, ite_false] at ih'
      have := hand pa na pb nb; omega
    · simp only [ite_true] at ih'
      have := hor pa na pb nb; omega
def phi (N a b1 b2 d e1 e2 : Nat) (pn : Nat × Nat) : Nat :=
  vf (pn.1.testBit (a * N + d)) (pn.1.testBit (b1 * N + d)) (pn.1.testBit (b2 * N + d))
     (pn.2.testBit (a * N + d)) (pn.2.testBit (a * N + e1)) (pn.2.testBit (a * N + e2))
lemma natTRestricted_phi {P N a b1 b2 d e1 e2 k : Nat} {ws : List (Nat × Nat × Nat)}
    (ha : a < P) (hb1 : b1 < P) (hb2 : b2 < P) (hd : d < N) (he1 : e1 < N) (he2 : e2 < N)
    (h : NatTRestricted (2 ^ (P * N) - 1) k ws) (hlen : ws.length = k + 1) :
    3 ≤ (ws.map fun w => phi N a b1 b2 d e1 e2 (w.1, w.2.1)).sum := by
  have hsub := natTRestricted_tight_subadd (phi N a b1 b2 d e1 e2)
    (fun p1 n1 p2 n2 => by simp only [phi, Nat.testBit_and]; exact vf_and _ _ _ _ _ _ _ _ _ _ _ _)
    (fun p1 n1 p2 n2 => by simp only [phi, Nat.testBit_or]; exact vf_or _ _ _ _ _ _ _ _ _ _ _ _)
    k ws h hlen
  have hlt : ∀ r c, r < P → c < N → r * N + c < P * N := by
    intro r c hr hc
    have : (r + 1) * N ≤ P * N := Nat.mul_le_mul_right N hr
    rw [Nat.add_mul, Nat.one_mul] at this; omega
  have h3 : phi N a b1 b2 d e1 e2 (2 ^ (P * N) - 1, 0) = 3 := by
    simp only [phi, Nat.testBit_two_pow_sub_one, Nat.zero_testBit,
      hlt a d ha hd, hlt b1 d hb1 hd, hlt b2 d hb2 hd, decide_true]
    rfl
  rwa [h3] at hsub
private lemma nat_land_eq (a b : Nat) : Nat.land a b = (a &&& b) := rfl
private lemma nat_lor_eq (a b : Nat) : Nat.lor a b = (a ||| b) := rfl
private lemma nat_xor_eq (a b : Nat) : Nat.xor a b = (a ^^^ b) := rfl
private lemma nat_shl_eq (a b : Nat) : Nat.shiftLeft a b = (a <<< b) := rfl
private lemma nat_shr_eq (a b : Nat) : Nat.shiftRight a b = (a >>> b) := rfl
private lemma nat_add_eq (a b : Nat) : Nat.add a b = (a + b) := rfl
private lemma nat_mul_eq (a b : Nat) : Nat.mul a b = (a * b) := rfl
def rowMask (m1 m2 m4 m8 rowStart rowFull uw : Nat) : Nat :=
  let r := Nat.lor uw (Nat.land (Nat.shiftRight uw 1) m1)
  let r := Nat.lor r (Nat.land (Nat.shiftRight r 2) m2)
  let r := Nat.lor r (Nat.land (Nat.shiftRight r 4) m4)
  let r := Nat.land (Nat.lor r (Nat.land (Nat.shiftRight r 8) m8)) rowStart
  Nat.mul r rowFull
def colMask (N rowStart rowFull uw : Nat) : Nat :=
  let c := Nat.lor uw (Nat.shiftRight uw (Nat.mul 8 N))
  let c := Nat.lor c (Nat.shiftRight c (Nat.mul 4 N))
  let c := Nat.lor c (Nat.shiftRight c (Nat.mul 2 N))
  let c := Nat.land (Nat.lor c (Nat.shiftRight c N)) rowFull
  Nat.mul c rowStart
def MaskLoOk (P N k m : Nat) : Prop :=
  ∀ i < P, ∀ j < N, m.testBit (i * N + j) = true → j + k < N
def RowStartOk (P N rs : Nat) : Prop :=
  rs < 2 ^ (P * N) ∧ ∀ k, rs.testBit k = true → k % N = 0
def checkRowStart (P N rs : Nat) : Bool :=
  Nat.blt rs (1 <<< (P * N)) &&
  (List.range (P * N)).all fun k => !rs.testBit k || Nat.beq (k % N) 0
lemma checkRowStart_ok {P N rs : Nat} (h : checkRowStart P N rs = true) : RowStartOk P N rs := by
  simp only [checkRowStart, Bool.and_eq_true, Nat.blt_eq, Nat.shiftLeft_eq, Nat.one_mul,
    List.all_eq_true, List.mem_range, Bool.or_eq_true, Bool.not_eq_true', Nat.beq_eq] at h
  refine ⟨h.1, fun k hk => ?_⟩
  have hlt : k < P * N := by
    by_contra hge
    have h2 : rs < 2 ^ k := Nat.lt_of_lt_of_le h.1 (Nat.pow_le_pow_right (by omega) (Nat.le_of_not_lt hge))
    rw [Nat.testBit_eq_false_of_lt h2] at hk; contradiction
  rcases h.2 k hlt with hf | hm
  · rw [hk] at hf; contradiction
  · exact hm
private lemma testBit_add_mul_two_pow_lo {N x y j : Nat} (hj : j < N) :
    (x + 2 ^ N * y).testBit j = x.testBit j := by
  rw [Nat.testBit, Nat.testBit, Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow]
  have hp : 2 ^ N = 2 ^ j * 2 ^ (N - j) := by rw [← Nat.pow_add, Nat.add_sub_cancel' (Nat.le_of_lt hj)]
  rw [hp, Nat.mul_assoc, Nat.add_mul_div_left _ _ (Nat.two_pow_pos j)]
  have hge1 : 1 ≤ N - j := by omega
  have h2 : 2 ^ (N - j) = 2 * 2 ^ (N - j - 1) := by
    conv_lhs => rw [← Nat.sub_add_cancel hge1, Nat.pow_succ, Nat.mul_comm]
  rw [h2, Nat.mul_assoc, Nat.one_and_eq_mod_two, Nat.one_and_eq_mod_two, Nat.add_mul_mod_self_left]
private lemma testBit_add_mul_two_pow_hi {N x y m : Nat} (hx : x < 2 ^ N) :
    (x + 2 ^ N * y).testBit (N + m) = y.testBit m := by
  rw [Nat.testBit, Nat.testBit, Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow,
    Nat.pow_add, ← Nat.div_div_eq_div_mul, Nat.add_mul_div_left _ _ (Nat.two_pow_pos N),
    Nat.div_eq_of_lt hx, Nat.zero_add]
private lemma aligned_mod_pow {N b : Nat} (hN : 0 < N) (hb : ∀ k, b.testBit k = true → k % N = 0) :
    b % 2 ^ N = if b.testBit 0 then 1 else 0 := by
  apply Nat.eq_of_testBit_eq; intro k
  rw [Nat.testBit_mod_two_pow]
  by_cases hk0 : k = 0
  · subst hk0; simp only [hN, decide_true, Bool.true_and]; cases b.testBit 0 <;> rfl
  · have h1f : (1 : Nat).testBit k = false :=
      Nat.testBit_eq_false_of_lt (Nat.lt_of_lt_of_le (by omega : 1 < 2 ^ 1) (Nat.pow_le_pow_right (by omega) (by omega)))
    by_cases hlt : k < N
    · simp only [hlt, decide_true, Bool.true_and]
      have hbf : b.testBit k = false := by
        cases hbk : b.testBit k
        · rfl
        · have hm := hb k hbk; rw [Nat.mod_eq_of_lt hlt] at hm; omega
      rw [hbf]; cases b.testBit 0 <;> simp [h1f]
    · simp only [hlt, decide_false, Bool.false_and]
      cases b.testBit 0 <;> simp [h1f]
private lemma mul_aligned_testBit {N : Nat} (hN : 0 < N) :
    ∀ (i a b j : Nat), a < 2 ^ N → (∀ k, b.testBit k = true → k % N = 0) → j < N →
      (a * b).testBit (i * N + j) = (a.testBit j && b.testBit (i * N)) := by
  intro i
  induction i with
  | zero =>
    intro a b j ha hb hj
    simp only [Nat.zero_mul, Nat.zero_add]
    have hdiv : b = b % 2 ^ N + 2 ^ N * (b / 2 ^ N) := (Nat.mod_add_div b (2 ^ N)).symm
    have hmod := aligned_mod_pow hN hb
    have heq : a * b = a * (b % 2 ^ N) + 2 ^ N * (a * (b / 2 ^ N)) := by
      conv_lhs => rw [hdiv]
      rw [Nat.mul_add, ← Nat.mul_assoc, Nat.mul_comm a (2 ^ N), Nat.mul_assoc]
    rw [heq, testBit_add_mul_two_pow_lo hj, hmod]; cases b.testBit 0 <;> simp
  | succ i ih =>
    intro a b j ha hb hj
    have hdiv : b = b % 2 ^ N + 2 ^ N * (b / 2 ^ N) := (Nat.mod_add_div b (2 ^ N)).symm
    have hmod := aligned_mod_pow hN hb
    have heq : a * b = a * (b % 2 ^ N) + 2 ^ N * (a * (b / 2 ^ N)) := by
      conv_lhs => rw [hdiv]
      rw [Nat.mul_add, ← Nat.mul_assoc, Nat.mul_comm a (2 ^ N), Nat.mul_assoc]
    have hlt2 : a * (b % 2 ^ N) < 2 ^ N := by rw [hmod]; cases b.testBit 0 <;> simp <;> omega
    have hidx : (i + 1) * N + j = N + (i * N + j) := by rw [Nat.add_mul, Nat.one_mul]; omega
    rw [heq, hidx, testBit_add_mul_two_pow_hi hlt2]
    have hb' : ∀ k, (b / 2 ^ N).testBit k = true → k % N = 0 := by
      intro k hk
      rw [← Nat.shiftRight_eq_div_pow, Nat.testBit_shiftRight] at hk
      have hm := hb (N + k) hk
      rwa [Nat.add_mod_left] at hm
    rw [ih a (b / 2 ^ N) j ha hb' hj, ← Nat.shiftRight_eq_div_pow, Nat.testBit_shiftRight]
    have hidx2 : N + i * N = (i + 1) * N := by rw [Nat.add_mul, Nat.one_mul]; omega
    rw [hidx2]
lemma lane_shr_sound {P N k m x i j : Nat} (hi : i < P) (hj : j < N)
    (hm : MaskLoOk P N k m) (h : (x ||| ((x >>> k) &&& m)).testBit (i * N + j) = true) :
    ∃ e < N, x.testBit (i * N + e) = true := by
  simp only [Nat.testBit_or, Nat.testBit_and, Nat.testBit_shiftRight, Bool.or_eq_true, Bool.and_eq_true] at h
  rcases h with hx | ⟨hx, hmk⟩
  · exact ⟨j, hj, hx⟩
  · refine ⟨j + k, hm i hi j hj hmk, ?_⟩
    have heq : k + (i * N + j) = i * N + (j + k) := by omega
    rwa [← heq]
lemma rowMask_sound {P N m1 m2 m4 m8 rowStart rowFull uw i j : Nat}
    (hN : 0 < N) (hrf : rowFull = (1 <<< N) - 1) (hrs : RowStartOk P N rowStart)
    (hm1 : MaskLoOk P N 1 m1) (hm2 : MaskLoOk P N 2 m2)
    (hm4 : MaskLoOk P N 4 m4) (hm8 : MaskLoOk P N 8 m8)
    (hi : i < P) (hj : j < N)
    (h : (rowMask m1 m2 m4 m8 rowStart rowFull uw).testBit (i * N + j) = true) :
    ∃ e < N, uw.testBit (i * N + e) = true := by
  unfold rowMask at h
  simp only [nat_lor_eq, nat_land_eq, nat_shr_eq, nat_mul_eq] at h
  have hrf_lt : rowFull < 2 ^ N := by
    rw [hrf, Nat.shiftLeft_eq, Nat.one_mul]; have := Nat.two_pow_pos N; omega
  have hal : ∀ k, ((((uw ||| uw >>> 1 &&& m1) ||| (uw ||| uw >>> 1 &&& m1) >>> 2 &&& m2) |||
      ((uw ||| uw >>> 1 &&& m1) ||| (uw ||| uw >>> 1 &&& m1) >>> 2 &&& m2) >>> 4 &&& m4 |||
      (((uw ||| uw >>> 1 &&& m1) ||| (uw ||| uw >>> 1 &&& m1) >>> 2 &&& m2) |||
      ((uw ||| uw >>> 1 &&& m1) ||| (uw ||| uw >>> 1 &&& m1) >>> 2 &&& m2) >>> 4 &&& m4) >>> 8 &&& m8) &&& rowStart).testBit k = true → k % N = 0 := by
    intro k hk; rw [Nat.testBit_and, Bool.and_eq_true] at hk; exact hrs.2 k hk.2
  rw [Nat.mul_comm, mul_aligned_testBit hN i rowFull _ j hrf_lt hal hj, Bool.and_eq_true] at h
  have h4 := h.2
  rw [Nat.testBit_and, Bool.and_eq_true] at h4
  have h4' : ((((uw ||| uw >>> 1 &&& m1) ||| (uw ||| uw >>> 1 &&& m1) >>> 2 &&& m2) |||
      ((uw ||| uw >>> 1 &&& m1) ||| (uw ||| uw >>> 1 &&& m1) >>> 2 &&& m2) >>> 4 &&& m4) |||
      ((((uw ||| uw >>> 1 &&& m1) ||| (uw ||| uw >>> 1 &&& m1) >>> 2 &&& m2) |||
      ((uw ||| uw >>> 1 &&& m1) ||| (uw ||| uw >>> 1 &&& m1) >>> 2 &&& m2) >>> 4 &&& m4) >>> 8 &&& m8)).testBit (i * N + 0) = true := by
    simpa using h4.1
  obtain ⟨e3, he3, h3⟩ := lane_shr_sound hi hN hm8 h4'
  obtain ⟨e2, he2, h2⟩ := lane_shr_sound hi he3 hm4 h3
  obtain ⟨e1, he1, h1⟩ := lane_shr_sound hi he2 hm2 h2
  exact lane_shr_sound hi he1 hm1 h1
lemma col_shr_sound {N k x i j : Nat}
    (h : (x ||| (x >>> (k * N))).testBit (i * N + j) = true) :
    ∃ r, x.testBit (r * N + j) = true := by
  simp only [Nat.testBit_or, Nat.testBit_shiftRight, Bool.or_eq_true] at h
  rcases h with hx | hx
  · exact ⟨i, hx⟩
  · refine ⟨i + k, ?_⟩
    have heq : k * N + (i * N + j) = (i + k) * N + j := by rw [Nat.add_mul]; omega
    rwa [← heq]
lemma colMask_sound {P N rowStart rowFull uw i j : Nat}
    (hN : 0 < N) (huw : uw < 2 ^ (P * N)) (hrf : rowFull = (1 <<< N) - 1) (hrs : RowStartOk P N rowStart)
    (hj : j < N) (h : (colMask N rowStart rowFull uw).testBit (i * N + j) = true) :
    ∃ b < P, uw.testBit (b * N + j) = true := by
  unfold colMask at h
  simp only [nat_lor_eq, nat_land_eq, nat_shr_eq, nat_mul_eq] at h
  have hc_lt : ((((uw ||| uw >>> (8 * N)) ||| (uw ||| uw >>> (8 * N)) >>> (4 * N)) |||
      ((uw ||| uw >>> (8 * N)) ||| (uw ||| uw >>> (8 * N)) >>> (4 * N)) >>> (2 * N) |||
      (((uw ||| uw >>> (8 * N)) ||| (uw ||| uw >>> (8 * N)) >>> (4 * N)) |||
      ((uw ||| uw >>> (8 * N)) ||| (uw ||| uw >>> (8 * N)) >>> (4 * N)) >>> (2 * N)) >>> N) &&& rowFull) < 2 ^ N := by
    have hrf_lt : rowFull < 2 ^ N := by rw [hrf, Nat.shiftLeft_eq, Nat.one_mul]; have := Nat.two_pow_pos N; omega
    exact Nat.lt_of_le_of_lt Nat.and_le_right hrf_lt
  rw [mul_aligned_testBit hN i _ rowStart j hc_lt hrs.2 hj, Bool.and_eq_true] at h
  have h4 := h.1
  rw [Nat.testBit_and, Bool.and_eq_true] at h4
  have h4' : (((uw ||| uw >>> (8 * N)) ||| (uw ||| uw >>> (8 * N)) >>> (4 * N)) |||
      ((uw ||| uw >>> (8 * N)) ||| (uw ||| uw >>> (8 * N)) >>> (4 * N)) >>> (2 * N) |||
      (((uw ||| uw >>> (8 * N)) ||| (uw ||| uw >>> (8 * N)) >>> (4 * N)) |||
      ((uw ||| uw >>> (8 * N)) ||| (uw ||| uw >>> (8 * N)) >>> (4 * N)) >>> (2 * N)) >>> (1 * N)).testBit (0 * N + j) = true := by
    simpa [Nat.one_mul] using h4.1
  obtain ⟨r3, h3⟩ := col_shr_sound h4'
  obtain ⟨r2, h2⟩ := col_shr_sound h3
  obtain ⟨r1, h1⟩ := col_shr_sound h2
  obtain ⟨b, hb⟩ := col_shr_sound h1
  have hbP : b < P := by
    by_contra hge; push Not at hge
    have hge' : P * N ≤ b * N + j := by
      have : P * N ≤ b * N := Nat.mul_le_mul_right N hge
      omega
    have := Nat.testBit_eq_false_of_lt (Nat.lt_of_lt_of_le huw (Nat.pow_le_pow_right (by omega) hge'))
    rw [hb] at this; contradiction
  exact ⟨b, hbP, hb⟩
def revApp {α : Type} : List α → List α → List α
  | [], ys => ys
  | x :: xs, ys => revApp xs (x :: ys)
lemma revApp_eq {α : Type} : ∀ (xs ys : List α), revApp xs ys = xs.reverse ++ ys
  | [], ys => rfl
  | x :: xs, ys => by simp [revApp, revApp_eq xs (x :: ys)]
lemma revApp_perm {α : Type} (xs ys : List α) : (revApp xs ys).Perm (xs ++ ys) := by
  rw [revApp_eq]; exact (List.reverse_perm xs).append_right ys
def listLen {α : Type} : List α → Nat → Nat
  | [], acc => acc
  | _ :: xs, acc => listLen xs (Nat.add acc 1)
lemma listLen_eq {α : Type} : ∀ (xs : List α) (acc : Nat), listLen xs acc = xs.length + acc
  | [], acc => by simp [listLen]
  | _ :: xs, acc => by simp [listLen, nat_add_eq, listLen_eq xs (acc + 1)]; omega
def bn (c : Bool) (x y : Nat) : Nat := match c with | true => x | false => y
def buildSeps (top : Nat) : List (Nat × Nat × Nat) → Nat → Nat → List (Nat × Nat × Nat × Nat) × Nat × Nat
  | [], c1, c2 => ([], c1, c2)
  | (p, n, t) :: rest, c1, c2 =>
    let s := Nat.land p (Nat.xor n top)
    let (ls, c1', c2') := buildSeps top rest (Nat.lor c1 s) (Nat.lor c2 (Nat.land c1 s))
    ((p, n, t, s) :: ls, c1', c2')
def buildSepsK (top : Nat) (k : List Nat → Nat → Nat → Bool) :
    List (Nat × Nat × Nat) → List Nat → Nat → Nat → Bool
  | [], acc, c1, c2 => k acc c1 c2
  | w :: rest, acc, c1, c2 =>
    let s := Nat.land w.1 (Nat.xor w.2.1 top)
    buildSepsK top k rest (s :: acc) (Nat.lor c1 s) (Nat.lor c2 (Nat.land c1 s))
lemma buildSepsK_eq (top : Nat) (k : List Nat → Nat → Nat → Bool) :
    ∀ (ws : List (Nat × Nat × Nat)) (acc : List Nat) (c1 c2 : Nat),
      buildSepsK top k ws acc c1 c2 =
      k (revApp (ws.map fun w => w.1 &&& (w.2.1 ^^^ top)) acc)
        (buildSeps top ws c1 c2).2.1 (buildSeps top ws c1 c2).2.2
  | [], acc, c1, c2 => rfl
  | w :: rest, acc, c1, c2 => by
    rcases w with ⟨p, n, t⟩
    simp only [buildSepsK, buildSeps, List.map_cons, revApp, nat_land_eq, nat_xor_eq, nat_lor_eq]
    exact buildSepsK_eq top k rest ((p &&& (n ^^^ top)) :: acc) _ _
lemma buildSeps_fst (top : Nat) (ws : List (Nat × Nat × Nat)) (c1 c2 : Nat) :
    (buildSeps top ws c1 c2).1 = ws.map fun (p, n, t) => (p, n, t, p &&& (n ^^^ top)) := by
  induction ws generalizing c1 c2 with
  | nil => rfl
  | cons w rest ih => rcases w with ⟨p, n, t⟩; simp [buildSeps, ih]
lemma buildSeps_c1 (top : Nat) (ws : List (Nat × Nat × Nat)) (c1 c2 : Nat) :
    (buildSeps top ws c1 c2).2.1 = c1 ||| sepsOr top ws := by
  induction ws generalizing c1 c2 with
  | nil => simp [buildSeps, sepsOr]
  | cons w rest ih =>
    rcases w with ⟨p, n, t⟩
    simp only [buildSeps, sepsOr, nat_land_eq, nat_lor_eq, nat_xor_eq, ih]
    apply Nat.eq_of_testBit_eq; intro k
    simp [Nat.testBit_or, Bool.or_assoc]
lemma buildSeps_c2_mon (top : Nat) (ws : List (Nat × Nat × Nat)) (c1 c2 k : Nat)
    (h : c2.testBit k = true) : (buildSeps top ws c1 c2).2.2.testBit k = true := by
  induction ws generalizing c1 c2 with
  | nil => exact h
  | cons w rest ih =>
    rcases w with ⟨p, n, t⟩
    exact ih _ _ (by simp [Nat.testBit_or, h])
lemma buildSeps_c2_of_c1_mem (top : Nat) (ws : List (Nat × Nat × Nat)) (c1 c2 k : Nat)
    (hc1 : c1.testBit k = true) (hmem : ∃ w ∈ ws, (w.1 &&& (w.2.1 ^^^ top)).testBit k = true) :
    (buildSeps top ws c1 c2).2.2.testBit k = true := by
  induction ws generalizing c1 c2 with
  | nil => rcases hmem with ⟨_, h, _⟩; simp at h
  | cons w rest ih =>
    rcases w with ⟨p, n, t⟩
    rcases hmem with ⟨w', hw', hwk⟩
    rcases List.mem_cons.1 hw' with rfl | hw'
    · exact buildSeps_c2_mon top rest _ _ k (by simp [Nat.testBit_or, Nat.testBit_and, hc1, hwk])
    · exact ih _ _ (by simp [Nat.testBit_or, hc1]) ⟨w', hw', hwk⟩
lemma buildSeps_c2_of_two (top : Nat) {ws : List (Nat × Nat × Nat)} {w1 w2 : Nat × Nat × Nat} {r : List (Nat × Nat × Nat)}
    (hp : ws.Perm (w1 :: w2 :: r)) (c1 c2 k : Nat)
    (h1 : (w1.1 &&& (w1.2.1 ^^^ top)).testBit k = true)
    (h2 : (w2.1 &&& (w2.2.1 ^^^ top)).testBit k = true) :
    (buildSeps top ws c1 c2).2.2.testBit k = true := by
  have hcnt : ws.countP (fun w => (w.1 &&& (w.2.1 ^^^ top)).testBit k) ≥ 2 := by
    rw [hp.countP_eq]; simp only [List.countP_cons, h1, h2, ite_true]; omega
  clear hp w1 w2 r h1 h2
  induction ws generalizing c1 c2 with
  | nil => simp at hcnt
  | cons w rest ih =>
    rcases w with ⟨p, n, t⟩
    by_cases hw : (p &&& (n ^^^ top)).testBit k = true
    · simp only [List.countP_cons, hw, ite_true] at hcnt
      have hpos : 0 < rest.countP (fun w => (w.1 &&& (w.2.1 ^^^ top)).testBit k) := by omega
      obtain ⟨w', hw', hwk⟩ := List.countP_pos_iff.1 hpos
      exact buildSeps_c2_of_c1_mem top rest _ _ k (by simp [Nat.testBit_or, hw]) ⟨w', hw', hwk⟩
    · simp only [List.countP_cons, hw] at hcnt
      exact ih _ _ hcnt
lemma unique_sep_no_other (top : Nat) {ws rest : List (Nat × Nat × Nat)} {w : Nat × Nat × Nat}
    (hp : ws.Perm (w :: rest)) (k : Nat)
    (hu : ((buildSeps top ws 0 0).2.1 ^^^ (buildSeps top ws 0 0).2.2).testBit k = true)
    (hw : (w.1 &&& (w.2.1 ^^^ top)).testBit k = true) :
    ∀ w' ∈ rest, (w'.1 &&& (w'.2.1 ^^^ top)).testBit k = false := by
  intro w' hw'
  by_contra hne
  have hwt : (w'.1 &&& (w'.2.1 ^^^ top)).testBit k = true := by
    cases h : (w'.1 &&& (w'.2.1 ^^^ top)).testBit k
    · exact absurd h hne
    · rfl
  have hp2 : ws.Perm (w :: w' :: rest.erase w') := by
    classical
    exact hp.trans ((List.perm_cons_erase hw').cons w)
  have hc2 := buildSeps_c2_of_two top hp2 0 0 k hw hwt
  have hc1 : (buildSeps top ws 0 0).2.1.testBit k = true := by
    rw [buildSeps_c1, Nat.testBit_or, sepsOr_perm top hp]
    simp [sepsOr, Nat.testBit_or, hw]
  rw [Nat.testBit_xor, hc1, hc2] at hu; simp at hu
def hasCrossAux (m1 m2 m4 m8 rowStart N rowFull u c2 : Nat) :
    List Nat → Nat → Nat → Bool
  | [], _, r2 => match Nat.beq r2 0 with | true => false | false => true
  | s :: rest, r1, r2 =>
    let uw := Nat.land u s
    match Nat.beq uw 0 with
    | true => hasCrossAux m1 m2 m4 m8 rowStart N rowFull u c2 rest r1 r2
    | false =>
      let sc := Nat.land s c2
      match Nat.beq sc 0 with
      | true => hasCrossAux m1 m2 m4 m8 rowStart N rowFull u c2 rest r1 r2
      | false =>
        let rm := Nat.land sc (rowMask m1 m2 m4 m8 rowStart rowFull uw)
        match Nat.beq rm 0 with
        | true => hasCrossAux m1 m2 m4 m8 rowStart N rowFull u c2 rest r1 r2
        | false =>
          let cr := Nat.land rm (colMask N rowStart rowFull uw)
          let r2' := Nat.lor r2 (Nat.land r1 cr)
          match Nat.beq r2' 0 with
          | false => true
          | true => hasCrossAux m1 m2 m4 m8 rowStart N rowFull u c2 rest (Nat.lor r1 cr) r2'
lemma nat_ne_zero_exists_testBit {x : Nat} (hx : x ≠ 0) : ∃ k, x.testBit k = true := by
  by_contra h; push Not at h
  apply hx
  apply Nat.eq_of_testBit_eq; intro k
  rw [Nat.zero_testBit]
  cases hk : x.testBit k
  · rfl
  · exact absurd hk (h k)
lemma hasCrossAux_witness (m1 m2 m4 m8 rowStart N rowFull u c2 : Nat) :
    ∀ (seps : List Nat) (r1 r2 : Nat),
      hasCrossAux m1 m2 m4 m8 rowStart N rowFull u c2 seps r1 r2 = true →
      (∃ k, r2.testBit k = true) ∨
      (∃ k, r1.testBit k = true ∧ ∃ s ∈ seps,
        (((s &&& c2) &&& rowMask m1 m2 m4 m8 rowStart rowFull (u &&& s)) &&& colMask N rowStart rowFull (u &&& s)).testBit k = true) ∨
      (∃ k s1 s2 rest, seps.Perm (s1 :: s2 :: rest) ∧
        (((s1 &&& c2) &&& rowMask m1 m2 m4 m8 rowStart rowFull (u &&& s1)) &&& colMask N rowStart rowFull (u &&& s1)).testBit k = true ∧
        (((s2 &&& c2) &&& rowMask m1 m2 m4 m8 rowStart rowFull (u &&& s2)) &&& colMask N rowStart rowFull (u &&& s2)).testBit k = true) := by
  intro seps
  induction seps with
  | nil =>
    intro r1 r2 h
    dsimp only [hasCrossAux] at h
    have hne : r2 ≠ 0 := fun h0 => by subst h0; simp at h
    exact Or.inl (nat_ne_zero_exists_testBit hne)
  | cons s rest ih =>
    intro r1 r2 h
    have lift_ih : hasCrossAux m1 m2 m4 m8 rowStart N rowFull u c2 rest r1 r2 = true →
        (∃ k, r2.testBit k = true) ∨
        (∃ k, r1.testBit k = true ∧ ∃ s' ∈ s :: rest,
          (((s' &&& c2) &&& rowMask m1 m2 m4 m8 rowStart rowFull (u &&& s')) &&& colMask N rowStart rowFull (u &&& s')).testBit k = true) ∨
        (∃ k s1 s2 r', (s :: rest).Perm (s1 :: s2 :: r') ∧
          (((s1 &&& c2) &&& rowMask m1 m2 m4 m8 rowStart rowFull (u &&& s1)) &&& colMask N rowStart rowFull (u &&& s1)).testBit k = true ∧
          (((s2 &&& c2) &&& rowMask m1 m2 m4 m8 rowStart rowFull (u &&& s2)) &&& colMask N rowStart rowFull (u &&& s2)).testBit k = true) := by
      intro hr
      rcases ih r1 r2 hr with h1 | ⟨k, hr1, s', hs', hcr⟩ | ⟨k, s1, s2, r', hp, h1, h2⟩
      · exact Or.inl h1
      · exact Or.inr (Or.inl ⟨k, hr1, s', List.mem_cons_of_mem _ hs', hcr⟩)
      · exact Or.inr (Or.inr ⟨k, s1, s2, s :: r',
          (hp.cons s).trans ((List.Perm.swap _ _ _).trans ((List.Perm.swap _ _ _).cons s1)), h1, h2⟩)
    dsimp only [hasCrossAux] at h
    simp only [nat_land_eq, nat_lor_eq] at h
    set uw := u &&& s
    cases huw0 : Nat.beq uw 0
    · simp only [huw0] at h
      set sc := s &&& c2
      cases hsc0 : Nat.beq sc 0
      · simp only [hsc0] at h
        set rm := sc &&& rowMask m1 m2 m4 m8 rowStart rowFull uw
        cases hrm0 : Nat.beq rm 0
        · simp only [hrm0] at h
          set cr := rm &&& colMask N rowStart rowFull uw
          set r2' := r2 ||| (r1 &&& cr)
          cases hr2' : Nat.beq r2' 0
          · have hne : r2' ≠ 0 := fun h0 => by rw [h0] at hr2'; simp at hr2'
            obtain ⟨k, hk⟩ := nat_ne_zero_exists_testBit hne
            dsimp only [r2'] at hk
            simp only [Nat.testBit_or, Nat.testBit_and, Bool.or_eq_true, Bool.and_eq_true] at hk
            rcases hk with h2k | ⟨h1k, hcrk⟩
            · exact Or.inl ⟨k, h2k⟩
            · exact Or.inr (Or.inl ⟨k, h1k, s, List.mem_cons_self, hcrk⟩)
          · simp only [hr2'] at h
            rcases ih (r1 ||| cr) r2' h with ⟨k, hk⟩ | ⟨k, hr1, s', hs', hcr⟩ | ⟨k, s1, s2, r', hp, h1, h2⟩
            · simp only [r2', Nat.testBit_or, Nat.testBit_and, Bool.or_eq_true, Bool.and_eq_true] at hk
              rcases hk with h2k | ⟨h1k, hcrk⟩
              · exact Or.inl ⟨k, h2k⟩
              · exact Or.inr (Or.inl ⟨k, h1k, s, List.mem_cons_self, hcrk⟩)
            · simp only [Nat.testBit_or, Bool.or_eq_true] at hr1
              rcases hr1 with h1k | hcrk
              · exact Or.inr (Or.inl ⟨k, h1k, s', List.mem_cons_of_mem _ hs', hcr⟩)
              · classical
                refine Or.inr (Or.inr ⟨k, s, s', rest.erase s',
                  ((List.perm_cons_erase hs').cons _), hcrk, hcr⟩)
            · exact Or.inr (Or.inr ⟨k, s1, s2, s :: r',
                (hp.cons s).trans ((List.Perm.swap _ _ _).trans ((List.Perm.swap _ _ _).cons s1)), h1, h2⟩)
        · simp only [hrm0] at h; exact lift_ih h
      · simp only [hsc0] at h; exact lift_ih h
    · simp only [huw0] at h; exact lift_ih h
lemma natTRestricted_no_cross {P N m1 m2 m4 m8 rowStart rowFull k : Nat}
    {ws : List (Nat × Nat × Nat)}
    (hN : 0 < N) (hrf : rowFull = (1 <<< N) - 1) (hrs : RowStartOk P N rowStart)
    (hm1 : MaskLoOk P N 1 m1) (hm2 : MaskLoOk P N 2 m2)
    (hm4 : MaskLoOk P N 4 m4) (hm8 : MaskLoOk P N 8 m8)
    (hrc : ∀ w ∈ ws, RowColConst P N w.1 w.2.1)
    (h : NatTRestricted (2 ^ (P * N) - 1) k ws)
    (hlen : ws.length = k + 1) :
    let top := 2 ^ (P * N) - 1
    let c1 := (buildSeps top ws 0 0).2.1
    let c2 := (buildSeps top ws 0 0).2.2
    let seps := ws.map fun w => w.1 &&& (w.2.1 ^^^ top)
    hasCrossAux m1 m2 m4 m8 rowStart N rowFull (c1 ^^^ c2) c2 seps 0 0 = false := by
  set top := 2 ^ (P * N) - 1
  dsimp only
  cases hcross : hasCrossAux m1 m2 m4 m8 rowStart N rowFull
      ((buildSeps top ws 0 0).2.1 ^^^ (buildSeps top ws 0 0).2.2) (buildSeps top ws 0 0).2.2
      (ws.map fun w => w.1 &&& (w.2.1 ^^^ top)) 0 0
  · rfl
  · exfalso
    set c1 := (buildSeps top ws 0 0).2.1
    set c2 := (buildSeps top ws 0 0).2.2
    set u := c1 ^^^ c2
    rcases hasCrossAux_witness m1 m2 m4 m8 rowStart N rowFull u c2 _ 0 0 hcross with
      ⟨idx, h0⟩ | ⟨idx, h0, _⟩ | ⟨idx, s1v, s2v, srest, hsp, hcr1, hcr2⟩
    · simp at h0
    · simp at h0
    · have hsp' : (ws.map fun w : Nat × Nat × Nat => w.1 &&& (w.2.1 ^^^ top)).Perm (s1v :: s2v :: srest) := hsp
      obtain ⟨l', hlp, hlm⟩ := perm_map_exists (fun w : Nat × Nat × Nat => w.1 &&& (w.2.1 ^^^ top)) hsp'
      cases l' with
      | nil => simp at hlm
      | cons w1 l1 =>
        cases l1 with
        | nil => simp at hlm
        | cons w2 wrest =>
          simp only [List.map_cons, List.cons.injEq] at hlm
          obtain ⟨rfl, rfl, _⟩ := hlm
          set s1 := w1.1 &&& (w1.2.1 ^^^ top)
          set s2 := w2.1 &&& (w2.2.1 ^^^ top)
          simp only [Nat.testBit_and, Bool.and_eq_true] at hcr1 hcr2
          have hs1_idx : s1.testBit idx = true := hcr1.1.1.1
          have hs2_idx : s2.testBit idx = true := hcr2.1.1.1
          have hidx_lt : idx < P * N := by
            have hw1 := hrc w1 (hlp.mem_iff.2 List.mem_cons_self)
            have hp1 : w1.1.testBit idx = true := by have h := hs1_idx; simp only [s1, Nat.testBit_and, Bool.and_eq_true] at h; exact h.1
            by_contra hge; push Not at hge
            have := Nat.testBit_eq_false_of_lt (Nat.lt_of_lt_of_le hw1.1 (Nat.pow_le_pow_right (by omega) hge))
            rw [hp1] at this; contradiction
          set a := idx / N
          set d := idx % N
          have hd : d < N := Nat.mod_lt idx hN
          have ha : a < P := by
            by_contra hge; push Not at hge
            have : P * N ≤ a * N := Nat.mul_le_mul_right N hge
            have : a * N + d = idx := by rw [Nat.mul_comm]; exact Nat.div_add_mod idx N
            omega
          have hidx_eq : idx = a * N + d := by rw [Nat.mul_comm]; exact (Nat.div_add_mod idx N).symm
          have huw1_lt : (u &&& s1) < 2 ^ (P * N) := by
            have hw1 := hrc w1 (hlp.mem_iff.2 List.mem_cons_self)
            exact Nat.lt_of_le_of_lt Nat.and_le_right (Nat.lt_of_le_of_lt Nat.and_le_left hw1.1)
          have huw2_lt : (u &&& s2) < 2 ^ (P * N) := by
            have hw2 := hrc w2 (hlp.mem_iff.2 (List.mem_cons_of_mem _ List.mem_cons_self))
            exact Nat.lt_of_le_of_lt Nat.and_le_right (Nat.lt_of_le_of_lt Nat.and_le_left hw2.1)
          rw [hidx_eq] at hcr1 hcr2 hs1_idx hs2_idx
          obtain ⟨e1, he1, hu1e⟩ := rowMask_sound hN hrf hrs hm1 hm2 hm4 hm8 ha hd hcr1.1.2
          obtain ⟨b1, hb1, hu1b⟩ := colMask_sound hN huw1_lt hrf hrs hd hcr1.2
          obtain ⟨e2, he2, hu2e⟩ := rowMask_sound hN hrf hrs hm1 hm2 hm4 hm8 ha hd hcr2.1.2
          obtain ⟨b2, hb2, hu2b⟩ := colMask_sound hN huw2_lt hrf hrs hd hcr2.2
          rw [Nat.testBit_and, Bool.and_eq_true] at hu1e hu1b hu2e hu2b
          have hno1e := unique_sep_no_other top hlp (a * N + e1) hu1e.1 hu1e.2
          have hno1b := unique_sep_no_other top hlp (b1 * N + d) hu1b.1 hu1b.2
          have hlp2 : ws.Perm (w2 :: w1 :: wrest) := hlp.trans (List.Perm.swap _ _ _)
          have hno2e := unique_sep_no_other top hlp2 (a * N + e2) hu2e.1 hu2e.2
          have hno2b := unique_sep_no_other top hlp2 (b2 * N + d) hu2b.1 hu2b.2
          have hsep_split : ∀ (p n pos : Nat), pos < P * N →
              (p &&& (n ^^^ top)).testBit pos = true → p.testBit pos = true ∧ n.testBit pos = false := by
            intro p n pos hlt hs
            rw [Nat.testBit_and, Nat.testBit_xor, Nat.testBit_two_pow_sub_one, decide_eq_true hlt, Bool.and_eq_true] at hs
            exact ⟨hs.1, by cases hn : n.testBit pos <;> simp [hn] at hs ⊢⟩
          have hsep_false_p : ∀ (w : Nat × Nat × Nat) (r c : Nat), w ∈ ws → r < P → c < N →
              (w.1 &&& (w.2.1 ^^^ top)).testBit (r * N + c) = false →
              w.2.1.testBit (a * N + c) = false → w.1.testBit (r * N + c) = false := by
            intro w r c hw hr hc hsf hnf
            have hwrc := hrc w hw
            have hlt : r * N + c < P * N := by
              have : (r + 1) * N ≤ P * N := Nat.mul_le_mul_right N hr
              rw [Nat.add_mul, Nat.one_mul] at this; omega
            rw [Nat.testBit_and, Nat.testBit_xor, Nat.testBit_two_pow_sub_one, decide_eq_true hlt] at hsf
            have hnc : w.2.1.testBit (r * N + c) = false := by
              rw [hwrc.2.2.2 r hr c hc, ← hwrc.2.2.2 a ha c hc]; exact hnf
            rw [hnc] at hsf; simpa using hsf
          have hsep_false_n : ∀ (w : Nat × Nat × Nat) (r c : Nat), w ∈ ws → r < P → c < N →
              (w.1 &&& (w.2.1 ^^^ top)).testBit (r * N + c) = false →
              w.1.testBit (r * N + d) = true → w.2.1.testBit (r * N + c) = true := by
            intro w r c hw hr hc hsf hpt
            have hwrc := hrc w hw
            have hlt : r * N + c < P * N := by
              have : (r + 1) * N ≤ P * N := Nat.mul_le_mul_right N hr
              rw [Nat.add_mul, Nat.one_mul] at this; omega
            rw [Nat.testBit_and, Nat.testBit_xor, Nat.testBit_two_pow_sub_one, decide_eq_true hlt] at hsf
            have hpr : w.1.testBit (r * N + c) = true := by
              rw [hwrc.2.2.1 r hr c hc, ← hwrc.2.2.1 r hr d hd]; exact hpt
            rw [hpr] at hsf
            cases hn : w.2.1.testBit (r * N + c) <;> simp [hn] at hsf ⊢
          have hlt_rc : ∀ r c, r < P → c < N → r * N + c < P * N := by
            intro r c hr hc; have : (r + 1) * N ≤ P * N := Nat.mul_le_mul_right N hr
            rw [Nat.add_mul, Nat.one_mul] at this; omega
          have hw1_mem : w1 ∈ ws := hlp.mem_iff.2 List.mem_cons_self
          have hw2_mem : w2 ∈ ws := hlp.mem_iff.2 (List.mem_cons_of_mem _ List.mem_cons_self)
          have hphi1 : phi N a b1 b2 d e1 e2 (w1.1, w1.2.1) = 1 := by
            have ⟨hp1a, hn1d⟩ := hsep_split w1.1 w1.2.1 (a * N + d) (hlt_rc a d ha hd) hs1_idx
            have ⟨hp1b1, _⟩ := hsep_split w1.1 w1.2.1 (b1 * N + d) (hlt_rc b1 d hb1 hd) hu1b.2
            have ⟨_, hn1e1⟩ := hsep_split w1.1 w1.2.1 (a * N + e1) (hlt_rc a e1 ha he1) hu1e.2
            have hp1b2 := hsep_false_p w1 b2 d hw1_mem hb2 hd (hno2b w1 List.mem_cons_self) hn1d
            have hn1e2 := hsep_false_n w1 a e2 hw1_mem ha he2 (hno2e w1 List.mem_cons_self) hp1a
            simp [phi, hp1a, hn1d, hp1b1, hp1b2, hn1e1, hn1e2, vf]
          have hphi2 : phi N a b1 b2 d e1 e2 (w2.1, w2.2.1) = 1 := by
            have ⟨hp2a, hn2d⟩ := hsep_split w2.1 w2.2.1 (a * N + d) (hlt_rc a d ha hd) hs2_idx
            have ⟨hp2b2, _⟩ := hsep_split w2.1 w2.2.1 (b2 * N + d) (hlt_rc b2 d hb2 hd) hu2b.2
            have ⟨_, hn2e2⟩ := hsep_split w2.1 w2.2.1 (a * N + e2) (hlt_rc a e2 ha he2) hu2e.2
            have hp2b1 := hsep_false_p w2 b1 d hw2_mem hb1 hd (hno1b w2 List.mem_cons_self) hn2d
            have hn2e1 := hsep_false_n w2 a e1 hw2_mem ha he1 (hno1e w2 List.mem_cons_self) hp2a
            simp [phi, hp2a, hn2d, hp2b1, hp2b2, hn2e1, hn2e2, vf]
          have hphi_rest : ∀ w ∈ wrest, phi N a b1 b2 d e1 e2 (w.1, w.2.1) = 0 := by
            intro w hw
            have hw_mem : w ∈ ws := hlp.mem_iff.2 (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hw))
            cases hpa : w.1.testBit (a * N + d) <;> cases hnd : w.2.1.testBit (a * N + d)
            · have hb1f := hsep_false_p w b1 d hw_mem hb1 hd (hno1b w (List.mem_cons_of_mem _ hw)) hnd
              have hb2f := hsep_false_p w b2 d hw_mem hb2 hd (hno2b w (List.mem_cons_of_mem _ hw)) hnd
              simp [phi, hpa, hnd, hb1f, hb2f, vf]
            · simp [phi, hpa, hnd, vf]
            · have hb1f := hsep_false_p w b1 d hw_mem hb1 hd (hno1b w (List.mem_cons_of_mem _ hw)) hnd
              have hb2f := hsep_false_p w b2 d hw_mem hb2 hd (hno2b w (List.mem_cons_of_mem _ hw)) hnd
              have he1t := hsep_false_n w a e1 hw_mem ha he1 (hno1e w (List.mem_cons_of_mem _ hw)) hpa
              have he2t := hsep_false_n w a e2 hw_mem ha he2 (hno2e w (List.mem_cons_of_mem _ hw)) hpa
              simp [phi, hpa, hnd, hb1f, hb2f, he1t, he2t, vf]
            · have he1t := hsep_false_n w a e1 hw_mem ha he1 (hno1e w (List.mem_cons_of_mem _ hw)) hpa
              have he2t := hsep_false_n w a e2 hw_mem ha he2 (hno2e w (List.mem_cons_of_mem _ hw)) hpa
              simp [phi, hpa, hnd, he1t, he2t, vf]
          have hsum0 : (wrest.map fun w => phi N a b1 b2 d e1 e2 (w.1, w.2.1)).sum = 0 := by
            suffices ∀ l : List (Nat × Nat × Nat), (∀ w ∈ l, phi N a b1 b2 d e1 e2 (w.1, w.2.1) = 0) →
                (l.map fun w => phi N a b1 b2 d e1 e2 (w.1, w.2.1)).sum = 0 from this wrest hphi_rest
            intro l hl; induction l with
            | nil => rfl
            | cons w t iht =>
              simp only [List.map_cons, List.sum_cons, hl w List.mem_cons_self, Nat.zero_add]
              exact iht (fun w' hw' => hl w' (List.mem_cons_of_mem _ hw'))
          have h3 := natTRestricted_phi ha hb1 hb2 hd he1 he2 h hlen
          rw [list_sum_perm (hlp.map _)] at h3
          simp only [List.map_cons, List.sum_cons, hphi1, hphi2, hsum0] at h3
          omega
def swapList (w : Nat) : List (Nat × Nat) → Nat
  | [] => 0
  | (m, d) :: rest =>
    (((w &&& m) <<< d) ||| ((w >>> d) &&& m)) ||| swapList w rest
def applyInv (fix : Nat) (swaps : List (Nat × Nat)) (w : Nat) : Nat :=
  (w &&& fix) ||| swapList w swaps
def invDisjAux (acc : Nat) : List (Nat × Nat) → Bool
  | [] => true
  | (m, d) :: rest =>
    let md := m <<< d
    Nat.beq (acc &&& m) 0 && Nat.beq (acc &&& md) 0 && Nat.beq (m &&& md) 0 &&
    invDisjAux ((acc ||| m) ||| md) rest
def invUnionAux (acc : Nat) : List (Nat × Nat) → Nat
  | [] => acc
  | (m, d) :: rest => invUnionAux ((acc ||| m) ||| (m <<< d)) rest
def invValid (top fix : Nat) (swaps : List (Nat × Nat)) : Bool :=
  invDisjAux fix swaps && Nat.beq (invUnionAux fix swaps) top
private lemma b_and_disj (a b c d : Bool) (h1 : (a && d) = false) (h2 : (b && c) = false) :
    ((a || c) && (b || d)) = ((a && b) || (c && d)) := by revert a b c d h1 h2; decide
private lemma b_swap_and (le a1 b1 m1 a2 b2 m2 : Bool)
    (h1 : (le && (a1 && m1) && (b2 && m2)) = false)
    (h2 : (le && (b1 && m1) && (a2 && m2)) = false) :
    ((le && ((a1 && b1) && m1)) || ((a2 && b2) && m2)) =
    (((le && (a1 && m1)) || (a2 && m2)) && ((le && (b1 && m1)) || (b2 && m2))) := by
  revert le a1 b1 m1 a2 b2 m2 h1 h2; decide
private lemma b_swap_or (le a1 b1 m1 a2 b2 m2 r1 r2 : Bool) :
    ((le && ((a1 || b1) && m1)) || ((a2 || b2) && m2) || (r1 || r2)) =
    (((le && (a1 && m1)) || (a2 && m2) || r1) || ((le && (b1 && m1)) || (b2 && m2) || r2)) := by
  revert le a1 b1 m1 a2 b2 m2 r1 r2; decide
private lemma b_fix_and (a b f s1 s2 : Bool) (h1 : (f && s1) = false) (h2 : (f && s2) = false) :
    (((a && b) && f) || (s1 && s2)) = (((a && f) || s1) && ((b && f) || s2)) := by
  revert a b f s1 s2 h1 h2; decide
private lemma b_fix_or (a b f s1 s2 : Bool) :
    (((a || b) && f) || (s1 || s2)) = (((a && f) || s1) || ((b && f) || s2)) := by
  revert a b f s1 s2; decide
lemma invDisjAux_mem {acc : Nat} {swaps : List (Nat × Nat)} (h : invDisjAux acc swaps = true) :
    ∀ p ∈ swaps, (acc &&& p.1) = 0 ∧ (acc &&& (p.1 <<< p.2)) = 0 ∧ (p.1 &&& (p.1 <<< p.2)) = 0 := by
  induction swaps generalizing acc with
  | nil => intro p hp; simp at hp
  | cons p rest ih =>
    rcases p with ⟨m, d⟩
    simp only [invDisjAux, Bool.and_eq_true, Nat.beq_eq] at h
    intro q hq
    rcases List.mem_cons.1 hq with rfl | hq
    · exact ⟨h.1.1.1, h.1.1.2, h.1.2⟩
    · obtain ⟨h1, h2, h3⟩ := ih h.2 q hq
      refine ⟨?_, ?_, h3⟩
      · apply Nat.eq_of_testBit_eq; intro k
        have h1k := congrArg (fun x => x.testBit k) h1
        simp only [Nat.testBit_and, Nat.testBit_or, Nat.zero_testBit] at h1k ⊢
        cases ha : acc.testBit k
        · rfl
        · rw [ha, Bool.true_or, Bool.true_or, Bool.true_and] at h1k; simp [h1k]
      · apply Nat.eq_of_testBit_eq; intro k
        have h2k := congrArg (fun x => x.testBit k) h2
        simp only [Nat.testBit_and, Nat.testBit_or, Nat.zero_testBit] at h2k ⊢
        cases ha : acc.testBit k
        · rfl
        · rw [ha, Bool.true_or, Bool.true_or, Bool.true_and] at h2k; simp [h2k]
lemma invUnionAux_or (acc : Nat) (swaps : List (Nat × Nat)) :
    invUnionAux acc swaps = acc ||| invUnionAux 0 swaps := by
  induction swaps generalizing acc with
  | nil => simp [invUnionAux]
  | cons p rest ih =>
    rcases p with ⟨m, d⟩
    simp only [invUnionAux]
    rw [ih ((acc ||| m) ||| (m <<< d)), ih ((0 ||| m) ||| (m <<< d))]
    apply Nat.eq_of_testBit_eq; intro k
    simp [Nat.testBit_or, Bool.or_assoc]
lemma applyInv_and_or_aux {acc : Nat} {swaps : List (Nat × Nat)}
    (hd : invDisjAux acc swaps = true) (a b : Nat) :
    (swapList (a &&& b) swaps = (swapList a swaps &&& swapList b swaps)) ∧
    (swapList (a ||| b) swaps = (swapList a swaps ||| swapList b swaps)) ∧
    (acc &&& swapList a swaps = 0) := by
  induction swaps generalizing acc a b with
  | nil => simp [swapList]
  | cons p rest ih =>
    rcases p with ⟨m, d⟩
    simp only [invDisjAux, Bool.and_eq_true, Nat.beq_eq] at hd
    obtain ⟨⟨⟨ham, hamd⟩, hmmd⟩, hrest⟩ := hd
    obtain ⟨ih_and, ih_or, ih_disj⟩ := ih hrest a b
    set ta := ((a &&& m) <<< d) ||| ((a >>> d) &&& m)
    set tb := ((b &&& m) <<< d) ||| ((b >>> d) &&& m)
    set tab := (((a &&& b) &&& m) <<< d) ||| (((a &&& b) >>> d) &&& m)
    have hdisj_self : ∀ x y, (((x &&& m) <<< d) &&& ((y >>> d) &&& m)) = 0 := by
      intro x y; apply Nat.eq_of_testBit_eq; intro k
      have hm0 := congrArg (fun z => z.testBit k) hmmd
      simp only [Nat.testBit_and, Nat.testBit_shiftLeft, Nat.zero_testBit] at hm0 ⊢
      cases hmk : m.testBit k
      · simp
      · simp only [hmk, Bool.true_and] at hm0
        cases hle : decide (d ≤ k)
        · simp [hle]
        · simp only [hle, Bool.true_and] at hm0 ⊢; simp [hm0]
    have htab_eq : tab = (ta &&& tb) := by
      apply Nat.eq_of_testBit_eq; intro k
      have hd1 := congrArg (fun z => z.testBit k) (hdisj_self a b)
      have hd2 := congrArg (fun z => z.testBit k) (hdisj_self b a)
      simp only [Nat.testBit_and, Nat.testBit_shiftLeft, Nat.testBit_shiftRight, Nat.zero_testBit] at hd1 hd2
      simp only [tab, ta, tb, Nat.testBit_or, Nat.testBit_and, Nat.testBit_shiftLeft, Nat.testBit_shiftRight]
      exact b_swap_and (decide (d ≤ k)) (a.testBit (k - d)) (b.testBit (k - d)) (m.testBit (k - d))
        (a.testBit (d + k)) (b.testBit (d + k)) (m.testBit k) hd1 hd2
    have hdisj_tr : ∀ x y, ((((x &&& m) <<< d) ||| ((x >>> d) &&& m)) &&& swapList y rest) = 0 := by
      intro x y
      have hy0 := (ih hrest y y).2.2
      apply Nat.eq_of_testBit_eq; intro k
      have h0 := congrArg (fun z => z.testBit k) hy0
      simp only [Nat.testBit_and, Nat.testBit_or, Nat.testBit_shiftLeft, Nat.zero_testBit] at h0 ⊢
      cases hyk : (swapList y rest).testBit k
      · simp
      · simp only [hyk, Bool.and_true, Bool.or_eq_false_iff] at h0
        have hm0 : m.testBit k = false := h0.1.2
        have hmd0 : (decide (d ≤ k) && m.testBit (k - d)) = false := h0.2
        rw [hm0]; simp only [Bool.and_false, Bool.or_false, Bool.and_true]
        cases hle : decide (d ≤ k)
        · simp
        · simp only [hle, Bool.true_and] at hmd0 ⊢; simp [hmd0]
    refine ⟨?_, ?_, ?_⟩
    · simp only [swapList]
      change tab ||| swapList (a &&& b) rest = (ta ||| swapList a rest) &&& (tb ||| swapList b rest)
      rw [htab_eq, ih_and]
      apply Nat.eq_of_testBit_eq; intro k
      have h1 := congrArg (fun z => z.testBit k) (hdisj_tr a b)
      have h2 := congrArg (fun z => z.testBit k) (hdisj_tr b a)
      simp only [Nat.testBit_and, Nat.zero_testBit] at h1 h2
      simp only [Nat.testBit_and, Nat.testBit_or]
      exact (b_and_disj (ta.testBit k) (tb.testBit k) ((swapList a rest).testBit k) ((swapList b rest).testBit k) h1 h2).symm
    · simp only [swapList, ih_or]
      apply Nat.eq_of_testBit_eq; intro k
      simp only [Nat.testBit_or, Nat.testBit_and, Nat.testBit_shiftLeft, Nat.testBit_shiftRight]
      exact b_swap_or (decide (d ≤ k)) (a.testBit (k - d)) (b.testBit (k - d)) (m.testBit (k - d))
        (a.testBit (d + k)) (b.testBit (d + k)) (m.testBit k) ((swapList a rest).testBit k) ((swapList b rest).testBit k)
    · apply Nat.eq_of_testBit_eq; intro k
      have h0 := congrArg (fun z => z.testBit k) ih_disj
      have h1 := congrArg (fun z => z.testBit k) ham
      have h2 := congrArg (fun z => z.testBit k) hamd
      simp only [swapList, Nat.testBit_and, Nat.testBit_or, Nat.testBit_shiftLeft, Nat.zero_testBit] at h0 h1 h2 ⊢
      cases ha : acc.testBit k
      · simp
      · simp only [ha, Bool.true_and, Bool.true_or] at h0 h1 h2 ⊢
        rw [h0, h1]; simp only [Bool.and_false, Bool.or_false]
        cases hle : decide (d ≤ k)
        · simp
        · simp only [hle, Bool.true_and] at h2 ⊢; simp [h2]
lemma applyInv_and_or {top fix : Nat} {swaps : List (Nat × Nat)}
    (hv : invValid top fix swaps = true) (a b : Nat) :
    applyInv fix swaps (a &&& b) = (applyInv fix swaps a &&& applyInv fix swaps b) ∧
    applyInv fix swaps (a ||| b) = (applyInv fix swaps a ||| applyInv fix swaps b) := by
  simp only [invValid, Bool.and_eq_true, Nat.beq_eq] at hv
  obtain ⟨h_and, h_or, h_disj_a⟩ := applyInv_and_or_aux hv.1 a b
  obtain ⟨_, _, h_disj_b⟩ := applyInv_and_or_aux hv.1 b a
  refine ⟨?_, ?_⟩
  · simp only [applyInv, h_and]
    apply Nat.eq_of_testBit_eq; intro k
    have h1 := congrArg (fun z => z.testBit k) h_disj_a
    have h2 := congrArg (fun z => z.testBit k) h_disj_b
    simp only [Nat.testBit_and, Nat.zero_testBit] at h1 h2
    simp only [Nat.testBit_and, Nat.testBit_or]
    exact b_fix_and (a.testBit k) (b.testBit k) (fix.testBit k) ((swapList a swaps).testBit k) ((swapList b swaps).testBit k) h1 h2
  · simp only [applyInv, h_or]
    apply Nat.eq_of_testBit_eq; intro k
    simp only [Nat.testBit_and, Nat.testBit_or]
    exact b_fix_or (a.testBit k) (b.testBit k) (fix.testBit k) ((swapList a swaps).testBit k) ((swapList b swaps).testBit k)
lemma swapList_zero_of_disj {w : Nat} {swaps : List (Nat × Nat)} {mask : Nat}
    (hw : (w &&& mask) = w)
    (hl : ∀ q ∈ swaps, (mask &&& q.1) = 0 ∧ (mask &&& (q.1 <<< q.2)) = 0) :
    swapList w swaps = 0 := by
  induction swaps with
  | nil => rfl
  | cons q rest ih =>
    rcases q with ⟨m, d⟩
    have hq := hl (m, d) List.mem_cons_self
    have hr := ih (fun q' hq' => hl q' (List.mem_cons_of_mem _ hq'))
    simp only [swapList, hr, Nat.or_zero]
    apply Nat.eq_of_testBit_eq; intro k
    simp only [Nat.testBit_or, Nat.testBit_and, Nat.testBit_shiftLeft, Nat.testBit_shiftRight, Nat.zero_testBit,
      Bool.or_eq_false_iff, Bool.and_eq_false_iff]
    constructor
    · by_cases hle : d ≤ k
      · right
        have hwk := congrArg (fun z => z.testBit (k - d)) hw
        have h0 := congrArg (fun z => z.testBit (k - d)) hq.1
        simp only [Nat.testBit_and, Nat.zero_testBit] at hwk h0
        cases h1 : w.testBit (k - d)
        · left; rfl
        · right
          rw [h1, Bool.true_and] at hwk
          rw [hwk, Bool.true_and] at h0; exact h0
      · left; simp [hle]
    · have hwk := congrArg (fun z => z.testBit (d + k)) hw
      have h0 := congrArg (fun z => z.testBit (d + k)) hq.2
      simp only [Nat.testBit_and, Nat.testBit_shiftLeft, Nat.zero_testBit,
        show d ≤ d + k by omega, show d + k - d = k by omega, decide_true, Bool.true_and] at hwk h0
      cases h1 : w.testBit (d + k)
      · left; rfl
      · right
        rw [h1, Bool.true_and] at hwk
        rw [hwk, Bool.true_and] at h0; exact h0
lemma single_swap_invol {m d w : Nat} (hmmd : (m &&& (m <<< d)) = 0) :
    let t := ((w &&& m) <<< d) ||| ((w >>> d) &&& m)
    (((t &&& m) <<< d) ||| ((t >>> d) &&& m)) = (w &&& (m ||| (m <<< d))) := by
  dsimp only
  apply Nat.eq_of_testBit_eq; intro k
  have hm0_k := congrArg (fun z => z.testBit k) hmmd
  have hm0_kd := congrArg (fun z => z.testBit (k - d)) hmmd
  have hm0_dk := congrArg (fun z => z.testBit (d + k)) hmmd
  simp only [Nat.testBit_and, Nat.testBit_shiftLeft, Nat.zero_testBit,
    show d ≤ d + k by omega, show d + k - d = k by omega, decide_true, Bool.true_and] at hm0_k hm0_kd hm0_dk
  simp only [Nat.testBit_or, Nat.testBit_and, Nat.testBit_shiftLeft, Nat.testBit_shiftRight,
    show d ≤ d + k by omega, show d + k - d = k by omega, decide_true, Bool.true_and]
  by_cases hle : d ≤ k
  · have hadd : d + (k - d) = k := by omega
    simp only [hle, decide_true, Bool.true_and, hadd] at hm0_k ⊢
    cases hmkd : m.testBit (k - d)
    · cases hmk : m.testBit k
      · simp
      · simp only [hmk, Bool.true_and, Bool.and_true, Bool.false_and, Bool.false_or, Bool.or_false] at hm0_dk ⊢
        simp [hm0_dk]
    · simp only [hmkd, Bool.and_true, Bool.true_and] at hm0_k hm0_kd ⊢
      rw [hm0_k]
      simp only [Bool.and_false, Bool.or_false, Bool.false_or]
      cases hle2 : decide (d ≤ k - d)
      · simp
      · simp only [hle2, Bool.true_and] at hm0_kd ⊢; simp [hm0_kd]
  · simp only [hle, decide_false, Bool.false_and, Bool.false_or, Bool.or_false]
    cases hmk : m.testBit k
    · simp
    · simp only [hmk, Bool.true_and, Bool.and_true] at hm0_dk ⊢; simp [hm0_dk]
lemma swapList_invol_aux {acc : Nat} {swaps : List (Nat × Nat)}
    (hd : invDisjAux acc swaps = true) (w : Nat) :
    swapList (swapList w swaps) swaps = (w &&& invUnionAux 0 swaps) := by
  induction swaps generalizing acc with
  | nil => simp [swapList, invUnionAux]
  | cons p rest ih =>
    rcases p with ⟨m, d⟩
    simp only [invDisjAux, Bool.and_eq_true, Nat.beq_eq] at hd
    obtain ⟨⟨⟨_, _⟩, hmmd⟩, hrest⟩ := hd
    set t := ((w &&& m) <<< d) ||| ((w >>> d) &&& m)
    set r := swapList w rest
    have h_sw_t_rest : swapList t rest = 0 := by
      apply swapList_zero_of_disj (mask := m ||| (m <<< d))
      · apply Nat.eq_of_testBit_eq; intro k
        simp only [t, Nat.testBit_and, Nat.testBit_or, Nat.testBit_shiftLeft, Nat.testBit_shiftRight]
        cases decide (d ≤ k) <;> cases w.testBit (k - d) <;> cases m.testBit (k - d) <;>
          cases w.testBit (d + k) <;> cases m.testBit k <;> simp
      · intro q hq
        obtain ⟨h1, h2, _⟩ := invDisjAux_mem hrest q hq
        refine ⟨?_, ?_⟩ <;> (apply Nat.eq_of_testBit_eq; intro j)
        · have h1j := congrArg (fun z => z.testBit j) h1
          simp only [Nat.testBit_and, Nat.testBit_or, Nat.zero_testBit] at h1j ⊢
          cases hqj : q.1.testBit j
          · simp
          · rw [hqj, Bool.and_true] at h1j; simp only [Bool.or_eq_false_iff] at h1j; simp [h1j.1.2, h1j.2]
        · have h2j := congrArg (fun z => z.testBit j) h2
          simp only [Nat.testBit_and, Nat.testBit_or, Nat.zero_testBit] at h2j ⊢
          cases hqj : (q.1 <<< q.2).testBit j
          · simp
          · rw [hqj, Bool.and_true] at h2j; simp only [Bool.or_eq_false_iff] at h2j; simp [h2j.1.2, h2j.2]
    have h_r_md : (((r &&& m) <<< d) ||| ((r >>> d) &&& m)) = 0 := by
      have hr0 := (applyInv_and_or_aux hrest w w).2.2
      apply Nat.eq_of_testBit_eq; intro k
      have h0a := congrArg (fun z => z.testBit (k - d)) hr0
      have h0b := congrArg (fun z => z.testBit (d + k)) hr0
      simp only [Nat.testBit_and, Nat.testBit_or, Nat.testBit_shiftLeft, Nat.testBit_shiftRight, Nat.zero_testBit] at h0a h0b ⊢
      simp only [Bool.or_eq_false_iff, Bool.and_eq_false_iff]
      constructor
      · by_cases hle : d ≤ k
        · right
          cases hm : m.testBit (k - d)
          · right; rfl
          · left; rw [hm, Bool.or_true, Bool.true_or, Bool.true_and] at h0a; exact h0a
        · left; simp [ge_iff_le, hle]
      · cases hm : m.testBit k
        · right; rfl
        · left
          simp only [show d ≤ d + k by omega, show d + k - d = k by omega, ge_iff_le, decide_true, Bool.true_and, hm, Bool.or_true] at h0b
          exact h0b
    have h_or_rest := (applyInv_and_or_aux hrest t r).2.1
    have h_split_md : ((((t ||| r) &&& m) <<< d) ||| (((t ||| r) >>> d) &&& m)) =
        ((((t &&& m) <<< d) ||| ((t >>> d) &&& m)) ||| (((r &&& m) <<< d) ||| ((r >>> d) &&& m))) := by
      apply Nat.eq_of_testBit_eq; intro k
      simp only [Nat.testBit_or, Nat.testBit_and, Nat.testBit_shiftLeft, Nat.testBit_shiftRight]
      simpa using b_swap_or (decide (d ≤ k)) (t.testBit (k - d)) (r.testBit (k - d)) (m.testBit (k - d))
        (t.testBit (d + k)) (r.testBit (d + k)) (m.testBit k) false false
    simp only [swapList]
    rw [h_split_md, single_swap_invol hmmd, h_r_md, Nat.or_zero, h_or_rest, h_sw_t_rest, Nat.zero_or, ih hrest]
    rw [invUnionAux, Nat.zero_or, invUnionAux_or (m ||| (m <<< d)) rest]
    apply Nat.eq_of_testBit_eq; intro k
    simp only [Nat.testBit_or, Nat.testBit_and]
    cases w.testBit k <;> cases m.testBit k <;> cases (m <<< d).testBit k <;>
      cases (invUnionAux 0 rest).testBit k <;> simp
lemma applyInv_invol {top fix : Nat} {swaps : List (Nat × Nat)}
    (hv : invValid top fix swaps = true) (w : Nat) :
    applyInv fix swaps (applyInv fix swaps w) = (w &&& top) := by
  simp only [invValid, Bool.and_eq_true, Nat.beq_eq] at hv
  obtain ⟨hdisj, hunion⟩ := hv
  have h_or := (applyInv_and_or_aux hdisj (w &&& fix) (swapList w swaps)).2.1
  have h_dw := (applyInv_and_or_aux hdisj w w).2.2
  have h_sw_wf : swapList (w &&& fix) swaps = 0 := by
    apply swapList_zero_of_disj (mask := fix)
    · apply Nat.eq_of_testBit_eq; intro k; simp [Nat.testBit_and, Bool.and_assoc]
    · intro q hq; obtain ⟨a, b, _⟩ := invDisjAux_mem hdisj q hq; exact ⟨a, b⟩
  simp only [applyInv]
  have h1 : (((w &&& fix) ||| swapList w swaps) &&& fix) = (w &&& fix) := by
    apply Nat.eq_of_testBit_eq; intro k
    have h0 := congrArg (fun z => z.testBit k) h_dw
    simp only [Nat.testBit_and, Nat.testBit_or, Nat.zero_testBit] at h0 ⊢
    cases hf : fix.testBit k
    · simp
    · rw [hf, Bool.true_and] at h0; simp [h0]
  rw [h1, h_or, h_sw_wf, Nat.zero_or, swapList_invol_aux hdisj w]
  rw [← hunion, invUnionAux_or fix swaps]
  apply Nat.eq_of_testBit_eq; intro k
  simp only [Nat.testBit_and, Nat.testBit_or]
  cases w.testBit k <;> cases fix.testBit k <;> cases (invUnionAux 0 swaps).testBit k <;> simp
lemma applyInv_zero (fix : Nat) (swaps : List (Nat × Nat)) :
    applyInv fix swaps 0 = 0 := by
  suffices swapList 0 swaps = 0 by simp [applyInv, this]
  induction swaps with
  | nil => rfl
  | cons p rest ih => rcases p with ⟨m, d⟩; simp [swapList, ih]
lemma applyInv_top {top fix : Nat} {swaps : List (Nat × Nat)}
    (hv : invValid top fix swaps = true) :
    applyInv fix swaps top = top := by
  simp only [invValid, Bool.and_eq_true, Nat.beq_eq] at hv
  have hle_top : ∀ q ∈ swaps, (q.1 &&& top = q.1) ∧ (((q.1 <<< q.2) &&& top) = (q.1 <<< q.2)) := by
    intro q hq
    have hu : ∀ acc l, q ∈ l → ∀ k, (q.1.testBit k = true → (invUnionAux acc l).testBit k = true) ∧
        ((q.1 <<< q.2).testBit k = true → (invUnionAux acc l).testBit k = true) := by
      intro acc l hl
      induction l generalizing acc with
      | nil => simp at hl
      | cons p r ihr =>
        rcases p with ⟨m, d⟩; intro k
        rcases List.mem_cons.1 hl with rfl | hr
        · rw [invUnionAux, invUnionAux_or]
          constructor <;> (intro hk; simp [Nat.testBit_or, hk])
        · exact ihr _ hr k
    have h1 := hu fix swaps hq
    rw [hv.2] at h1
    constructor <;> (apply Nat.eq_of_testBit_eq; intro k; rw [Nat.testBit_and])
    · cases hqk : q.1.testBit k
      · simp
      · simp [(h1 k).1 hqk]
    · cases hqk : (q.1 <<< q.2).testBit k
      · simp
      · simp [(h1 k).2 hqk]
  have hsw_top : ∀ l : List (Nat × Nat), (∀ q ∈ l, (q.1 &&& top = q.1) ∧ (((q.1 <<< q.2) &&& top) = (q.1 <<< q.2))) →
      swapList top l = invUnionAux 0 l := by
    intro l hl
    induction l with
    | nil => simp [swapList, invUnionAux]
    | cons p r ihr =>
      rcases p with ⟨m, d⟩
      have hp := hl (m, d) List.mem_cons_self
      have hr := ihr (fun q hq => hl q (List.mem_cons_of_mem _ hq))
      simp only [swapList, invUnionAux, Nat.zero_or, hr]
      have h1 : (top &&& m) = m := by rw [Nat.and_comm]; exact hp.1
      have h2 : ((top >>> d) &&& m) = m := by
        apply Nat.eq_of_testBit_eq; intro k
        have hmd := congrArg (fun z => z.testBit (d + k)) hp.2
        simp only [Nat.testBit_and, Nat.testBit_shiftLeft, Nat.testBit_shiftRight,
          show d ≤ d + k by omega, show d + k - d = k by omega, decide_true, Bool.true_and] at hmd ⊢
        cases hm : m.testBit k <;> simp_all
      rw [h1, h2, invUnionAux_or (m ||| (m <<< d)) r]
      apply Nat.eq_of_testBit_eq; intro k; simp [Nat.testBit_or, Bool.or_comm]
  have hfix : (top &&& fix) = fix := by
    apply Nat.eq_of_testBit_eq; intro k
    have h0 := congrArg (fun z => z.testBit k) hv.2
    rw [invUnionAux_or, Nat.testBit_or] at h0
    rw [Nat.testBit_and]; cases hf : fix.testBit k
    · simp
    · rw [hf, Bool.true_or] at h0; simp [← h0]
  unfold applyInv
  rw [hfix, hsw_top swaps hle_top, ← invUnionAux_or, hv.2]
lemma natTRestricted_inv {M fixP fixN : Nat} {swapsP swapsN : List (Nat × Nat)}
    (hvP : invValid (2 ^ M - 1) fixP swapsP = true)
    (hvN : invValid (2 ^ M - 1) fixN swapsN = true) :
    ∀ k ws, (∀ w ∈ ws, w.1 < 2 ^ M ∧ w.2.1 < 2 ^ M) →
      NatTRestricted (2 ^ M - 1) k ws →
      NatTRestricted (2 ^ M - 1) k
        (ws.map fun (p, n, t) => (applyInv fixP swapsP p, applyInv fixN swapsN n, t)) := by
  set top := 2 ^ M - 1
  have hand_top : ∀ x, x < 2 ^ M → (x &&& top) = x := by
    intro x hx; apply Nat.eq_of_testBit_eq; intro k
    rw [Nat.testBit_and, Nat.testBit_two_pow_sub_one]
    by_cases hk : k < M
    · simp [hk]
    · have h0 := Nat.testBit_eq_false_of_lt (Nat.lt_of_lt_of_le hx (Nat.pow_le_pow_right (by omega) (Nat.le_of_not_lt hk)))
      simp [hk, h0]
  have hfP_inj : ∀ x y, x < 2 ^ M → y < 2 ^ M → applyInv fixP swapsP x = applyInv fixP swapsP y → x = y := by
    intro x y hx hy h
    have h1 := congrArg (applyInv fixP swapsP) h
    rw [applyInv_invol hvP x, applyInv_invol hvP y, hand_top x hx, hand_top y hy] at h1
    exact h1
  have hfN_inj : ∀ x y, x < 2 ^ M → y < 2 ^ M → applyInv fixN swapsN x = applyInv fixN swapsN y → x = y := by
    intro x y hx hy h
    have h1 := congrArg (applyInv fixN swapsN) h
    rw [applyInv_invol hvN x, applyInv_invol hvN y, hand_top x hx, hand_top y hy] at h1
    exact h1
  have htop_lt : top < 2 ^ M := by have : 0 < 2 ^ M := Nat.two_pow_pos M; omega
  intro k
  induction k with
  | zero =>
    rintro ws _ ⟨t, rfl⟩
    exact ⟨t, by simp [applyInv_top hvP, applyInv_zero]⟩
  | succ k ih =>
    intro ws hlt ⟨pa, na, ta, pb, nb, tb, rest, isOr, ka, kb, hp, h1, h2, h3, hgp, hgn, hdom, hrec⟩
    have ha_lt := hlt (pa, na, ta) (hp.mem_iff.2 List.mem_cons_self)
    have hb_lt := hlt (pb, nb, tb) (hp.mem_iff.2 (List.mem_cons_of_mem _ List.mem_cons_self))
    let gp := if isOr then (pa ||| pb) else (pa &&& pb)
    let gn := if isOr then (na ||| nb) else (na &&& nb)
    have hgp_lt : gp < 2 ^ M := by
      cases isOr
      · exact Nat.lt_of_le_of_lt Nat.and_le_left ha_lt.1
      · exact Nat.or_lt_two_pow ha_lt.1 hb_lt.1
    have hgn_lt : gn < 2 ^ M := by
      cases isOr
      · exact Nat.lt_of_le_of_lt Nat.and_le_left ha_lt.2
      · exact Nat.or_lt_two_pow ha_lt.2 hb_lt.2
    have hfgp : applyInv fixP swapsP gp = if isOr then (applyInv fixP swapsP pa ||| applyInv fixP swapsP pb) else (applyInv fixP swapsP pa &&& applyInv fixP swapsP pb) := by
      cases isOr <;> simp only [gp, ite_true, ite_false, Bool.false_eq_true]
      · exact (applyInv_and_or hvP pa pb).1
      · exact (applyInv_and_or hvP pa pb).2
    have hfgn : applyInv fixN swapsN gn = if isOr then (applyInv fixN swapsN na ||| applyInv fixN swapsN nb) else (applyInv fixN swapsN na &&& applyInv fixN swapsN nb) := by
      cases isOr <;> simp only [gn, ite_true, ite_false, Bool.false_eq_true]
      · exact (applyInv_and_or hvN na nb).1
      · exact (applyInv_and_or hvN na nb).2
    have hlt' : ∀ w ∈ (gp, gn, if !isOr && (Nat.beq ta 1 || Nat.beq tb 1) then 2 else 0) ::
        kept ka (pa, na, if isOr && Nat.beq ta 1 then 2 else ta)
          (kept kb (pb, nb, if isOr && Nat.beq tb 1 then 2 else tb) rest), w.1 < 2 ^ M ∧ w.2.1 < 2 ^ M := by
      intro w hw
      rcases List.mem_cons.1 hw with rfl | hw
      · exact ⟨hgp_lt, hgn_lt⟩
      · cases ka <;> cases kb <;> simp only [kept, ite_true, ite_false, Bool.false_eq_true, List.mem_cons] at hw
        · exact hlt w (hp.mem_iff.2 (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hw)))
        · rcases hw with rfl | hw
          · exact hb_lt
          · exact hlt w (hp.mem_iff.2 (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hw)))
        · rcases hw with rfl | hw
          · exact ha_lt
          · exact hlt w (hp.mem_iff.2 (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hw)))
        · rcases hw with rfl | rfl | hw
          · exact ha_lt
          · exact hb_lt
          · exact hlt w (hp.mem_iff.2 (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hw)))
    have hrec' := ih _ hlt' hrec
    have hmap_eq : (((gp, gn, if !isOr && (Nat.beq ta 1 || Nat.beq tb 1) then 2 else 0) ::
        kept ka (pa, na, if isOr && Nat.beq ta 1 then 2 else ta)
          (kept kb (pb, nb, if isOr && Nat.beq tb 1 then 2 else tb) rest)).map
          fun (p, n, t) => (applyInv fixP swapsP p, applyInv fixN swapsN n, t)) =
        ((if isOr then applyInv fixP swapsP pa ||| applyInv fixP swapsP pb else applyInv fixP swapsP pa &&& applyInv fixP swapsP pb,
          if isOr then applyInv fixN swapsN na ||| applyInv fixN swapsN nb else applyInv fixN swapsN na &&& applyInv fixN swapsN nb,
          if !isOr && (Nat.beq ta 1 || Nat.beq tb 1) then 2 else 0) ::
         kept ka (applyInv fixP swapsP pa, applyInv fixN swapsN na, if isOr && Nat.beq ta 1 then 2 else ta)
           (kept kb (applyInv fixP swapsP pb, applyInv fixN swapsN nb, if isOr && Nat.beq tb 1 then 2 else tb)
             (rest.map fun (p, n, t) => (applyInv fixP swapsP p, applyInv fixN swapsN n, t)))) := by
      cases ka <;> cases kb <;> simp [kept, hfgp, hfgn]
    rw [hmap_eq] at hrec'
    refine ⟨applyInv fixP swapsP pa, applyInv fixN swapsN na, ta, applyInv fixP swapsP pb, applyInv fixN swapsN nb, tb,
      rest.map fun (p, n, t) => (applyInv fixP swapsP p, applyInv fixN swapsN n, t),
      isOr, ka, kb, hp.map _, h1, h2, h3, ?_, ?_, ?_, hrec'⟩
    · intro h0; rw [← hfgp] at h0; exact hgp (hfP_inj gp 0 hgp_lt (Nat.two_pow_pos M) (h0.trans (applyInv_zero _ _).symm))
    · intro ht; rw [← hfgn] at ht; exact hgn (hfN_inj gn top hgn_lt htop_lt (ht.trans (applyInv_top hvN).symm))
    · intro w hw ⟨hdp, hdn⟩
      rw [List.mem_map] at hw; obtain ⟨w0, hw0, rfl⟩ := hw
      have hw0_lt := hlt w0 hw0
      rw [← hfgp, ← (applyInv_and_or hvP gp w0.1).1] at hdp
      rw [← hfgn, ← (applyInv_and_or hvN w0.2.1 gn).1] at hdn
      have hdp' := hfP_inj (gp &&& w0.1) gp (Nat.lt_of_le_of_lt Nat.and_le_left hgp_lt) hgp_lt hdp
      have hdn' := hfN_inj (w0.2.1 &&& gn) w0.2.1 (Nat.lt_of_le_of_lt Nat.and_le_left hw0_lt.2) hw0_lt.2 hdn
      exact hdom w0 hw0 ⟨hdp', hdn'⟩
def isRowConstMask (P N m : Nat) : Bool :=
  (List.range P).all fun i => (List.range N).all fun j => m.testBit (i * N + j) == m.testBit (i * N)
def rowInvOk (P N fix : Nat) (swaps : List (Nat × Nat)) : Bool :=
  isRowConstMask P N fix && swaps.all fun (m, d) => isRowConstMask P N m && Nat.beq (d % N) 0
def isColConstMask (P N m : Nat) : Bool :=
  (List.range P).all fun i => (List.range N).all fun j => m.testBit (i * N + j) == m.testBit j
def colInvOk (P N fix : Nat) (swaps : List (Nat × Nat)) : Bool :=
  isColConstMask P N fix && swaps.all fun (m, d) =>
    isColConstMask P N m && (List.range N).all fun j => !m.testBit j || decide (j + d < N)
lemma isRowConstMask_ok {P N m : Nat} (h : isRowConstMask P N m = true) :
    ∀ i < P, ∀ j < N, m.testBit (i * N + j) = m.testBit (i * N) := by
  intro i hi j hj
  simp only [isRowConstMask, List.all_eq_true, List.mem_range, beq_iff_eq] at h
  exact h i hi j hj
lemma isColConstMask_ok {P N m : Nat} (h : isColConstMask P N m = true) :
    ∀ i < P, ∀ j < N, m.testBit (i * N + j) = m.testBit j := by
  intro i hi j hj
  simp only [isColConstMask, List.all_eq_true, List.mem_range, beq_iff_eq] at h
  exact h i hi j hj
lemma applyInv_lt {M fix : Nat} {swaps : List (Nat × Nat)}
    (hv : invValid (2 ^ M - 1) fix swaps = true) {w : Nat} (hw : w < 2 ^ M) :
    applyInv fix swaps w < 2 ^ M := by
  have hand : (w &&& (2 ^ M - 1)) = w := by
    apply Nat.eq_of_testBit_eq; intro k
    rw [Nat.testBit_and, Nat.testBit_two_pow_sub_one]
    by_cases hk : k < M
    · simp [hk]
    · have h0 := Nat.testBit_eq_false_of_lt (Nat.lt_of_lt_of_le hw (Nat.pow_le_pow_right (by omega) (Nat.le_of_not_lt hk)))
      simp [hk, h0]
  have h1 : (applyInv fix swaps w &&& (2 ^ M - 1)) = applyInv fix swaps w := by
    rw [← applyInv_top hv, ← (applyInv_and_or hv w (2 ^ M - 1)).1, hand]
  have hle : applyInv fix swaps w ≤ 2 ^ M - 1 := h1 ▸ Nat.and_le_right
  have hpos : 0 < 2 ^ M := Nat.two_pow_pos M
  omega
lemma swapList_rowConst {P N w : Nat} {swaps : List (Nat × Nat)}
    (hw : w < 2 ^ (P * N) ∧ ∀ i < P, ∀ j < N, w.testBit (i * N + j) = w.testBit (i * N))
    (hsw : ∀ p ∈ swaps, (∀ i < P, ∀ j < N, p.1.testBit (i * N + j) = p.1.testBit (i * N)) ∧ p.2 % N = 0 ∧ p.1 < 2 ^ (P * N)) :
    ∀ i < P, ∀ j < N, (swapList w swaps).testBit (i * N + j) = (swapList w swaps).testBit (i * N) := by
  induction swaps with
  | nil => intro i _ j _; simp [swapList]
  | cons p rest ih =>
    rcases p with ⟨m, d⟩
    obtain ⟨hmrc, hdmod, hmlt⟩ := hsw (m, d) List.mem_cons_self
    have ihr := ih (fun q hq => hsw q (List.mem_cons_of_mem _ hq))
    intro i hi j hj
    have hN : 0 < N := by omega
    have hq : d = (d / N) * N := by have := Nat.div_add_mod d N; rw [hdmod, Nat.add_zero, Nat.mul_comm] at this; exact this.symm
    set q := d / N
    simp only [swapList, Nat.testBit_or, Nat.testBit_and, Nat.testBit_shiftLeft, Nat.testBit_shiftRight, ihr i hi j hj, hmrc i hi j hj]
    have hshl : (decide (d ≤ i * N + j) && (w.testBit (i * N + j - d) && m.testBit (i * N + j - d))) =
        (decide (d ≤ i * N) && (w.testBit (i * N - d) && m.testBit (i * N - d))) := by
      rw [hq]
      by_cases hqi : q ≤ i
      · have hle1 : q * N ≤ i * N := Nat.mul_le_mul_right N hqi
        have hle2 : q * N ≤ i * N + j := by omega
        have heq1 : i * N + j - q * N = (i - q) * N + j := by rw [Nat.sub_mul]; exact Nat.sub_add_comm hle1
        have heq2 : i * N - q * N = (i - q) * N := by rw [Nat.sub_mul]
        have hiq : i - q < P := Nat.lt_of_le_of_lt (Nat.sub_le i q) hi
        simp only [hle1, hle2, decide_true, Bool.true_and, heq1, heq2, hw.2 (i - q) hiq j hj, hmrc (i - q) hiq j hj]
      · have hilt : i + 1 ≤ q := by omega
        have hgt : (i + 1) * N ≤ q * N := Nat.mul_le_mul_right N hilt
        rw [Nat.add_mul, Nat.one_mul] at hgt
        have h1 : ¬ (q * N ≤ i * N + j) := by omega
        have h2 : ¬ (q * N ≤ i * N) := by omega
        simp [h1, h2]
    have hshr : w.testBit (d + (i * N + j)) = w.testBit (d + i * N) := by
      rw [hq]
      have heq1 : q * N + (i * N + j) = (q + i) * N + j := by rw [Nat.add_mul]; omega
      have heq2 : q * N + i * N = (q + i) * N := by rw [Nat.add_mul]
      rw [heq1, heq2]
      by_cases hqi : q + i < P
      · exact hw.2 (q + i) hqi j hj
      · have hge1 : P * N ≤ (q + i) * N := Nat.mul_le_mul_right N (Nat.le_of_not_lt hqi)
        have h0a := Nat.testBit_eq_false_of_lt (Nat.lt_of_lt_of_le hw.1 (Nat.pow_le_pow_right (by omega) (by omega : P * N ≤ (q + i) * N + j)))
        have h0b := Nat.testBit_eq_false_of_lt (Nat.lt_of_lt_of_le hw.1 (Nat.pow_le_pow_right (by omega) hge1))
        rw [h0a, h0b]
    rw [hshl, hshr]
lemma swapList_colConst {P N w : Nat} {swaps : List (Nat × Nat)}
    (hw : w < 2 ^ (P * N) ∧ ∀ i < P, ∀ j < N, w.testBit (i * N + j) = w.testBit j)
    (hsw : ∀ p ∈ swaps, (∀ i < P, ∀ j < N, p.1.testBit (i * N + j) = p.1.testBit j) ∧
      (∀ j < N, p.1.testBit j = true → j + p.2 < N) ∧ p.1 < 2 ^ (P * N)) :
    ∀ i < P, ∀ j < N, (swapList w swaps).testBit (i * N + j) = (swapList w swaps).testBit j := by
  induction swaps with
  | nil => intro i _ j _; simp [swapList]
  | cons p rest ih =>
    rcases p with ⟨m, d⟩
    obtain ⟨hmcc, hmd, hmlt⟩ := hsw (m, d) List.mem_cons_self
    have ihr := ih (fun q hq => hsw q (List.mem_cons_of_mem _ hq))
    intro i hi j hj
    simp only [swapList, Nat.testBit_or, Nat.testBit_and, Nat.testBit_shiftLeft, Nat.testBit_shiftRight, ihr i hi j hj, hmcc i hi j hj]
    have hshl : (decide (d ≤ i * N + j) && (w.testBit (i * N + j - d) && m.testBit (i * N + j - d))) =
        (decide (d ≤ j) && (w.testBit (j - d) && m.testBit (j - d))) := by
      by_cases hdj : d ≤ j
      · have hle1 : d ≤ i * N + j := by omega
        have heq1 : i * N + j - d = i * N + (j - d) := by omega
        have hjd : j - d < N := by omega
        simp only [hdj, hle1, decide_true, Bool.true_and, heq1, hw.2 i hi (j - d) hjd, hmcc i hi (j - d) hjd]
      · simp only [hdj, decide_false, Bool.false_and]
        by_cases hle1 : d ≤ i * N + j
        · simp only [hle1, decide_true, Bool.true_and]
          have hmf : m.testBit (i * N + j - d) = false := by
            by_cases hlt : i * N + j - d < P * N
            · have hN : 0 < N := by omega
              set r := (i * N + j - d) / N
              set c := (i * N + j - d) % N
              have hc : c < N := Nat.mod_lt _ hN
              have hdiv : i * N + j - d = r * N + c := by have h := Nat.div_add_mod (i * N + j - d) N; rw [Nat.mul_comm] at h; exact h.symm
              have hrP : r < P := by
                by_contra hge; push Not at hge
                have : P * N ≤ r * N := Nat.mul_le_mul_right N hge
                omega
              rw [hdiv, hmcc r hrP c hc]
              cases hmc : m.testBit c
              · rfl
              · exfalso
                have hcd := hmd c hc hmc
                have hsum : r * N + (c + d) = i * N + j := by omega
                have hri : r = i := by
                  have h1 : (r * N + (c + d)) / N = r := by
                    rw [Nat.mul_comm, Nat.mul_add_div hN, Nat.div_eq_of_lt hcd, Nat.add_zero]
                  have h2 : (i * N + j) / N = i := by
                    rw [Nat.mul_comm, Nat.mul_add_div hN, Nat.div_eq_of_lt hj, Nat.add_zero]
                  rw [← h1, hsum, h2]
                rw [hri] at hsum; omega
            · exact Nat.testBit_eq_false_of_lt (Nat.lt_of_lt_of_le hmlt (Nat.pow_le_pow_right (by omega) (Nat.le_of_not_lt hlt)))
          rw [hmf, Bool.and_false]
        · simp [hle1]
    have hshr : (w.testBit (d + (i * N + j)) && m.testBit j) = (w.testBit (d + j) && m.testBit j) := by
      cases hmj : m.testBit j
      · simp
      · have hjd := hmd j hj hmj
        have heq1 : d + (i * N + j) = i * N + (j + d) := by omega
        have heq2 : d + j = j + d := by omega
        rw [heq1, heq2, hw.2 i hi (j + d) hjd]
    rw [hshl, hshr]
lemma invValid_mem_lt {M fix : Nat} {swaps : List (Nat × Nat)}
    (hv : invValid (2 ^ M - 1) fix swaps = true) :
    ∀ q ∈ swaps, q.1 < 2 ^ M := by
  simp only [invValid, Bool.and_eq_true, Nat.beq_eq] at hv
  intro q hq
  apply Nat.lt_pow_two_of_testBit
  intro k hk
  have hu : ∀ acc l, q ∈ l → q.1.testBit k = true → (invUnionAux acc l).testBit k = true := by
    intro acc l hl hqk
    induction l generalizing acc with
    | nil => simp at hl
    | cons p r ihr =>
      rcases p with ⟨m, d⟩
      rcases List.mem_cons.1 hl with rfl | hr
      · rw [invUnionAux, invUnionAux_or]; simp [Nat.testBit_or, hqk]
      · exact ihr _ hr
  cases hqk : q.1.testBit k
  · rfl
  · have h1 := hu fix swaps hq hqk
    rw [hv.2, Nat.testBit_two_pow_sub_one] at h1
    have : k < M := of_decide_eq_true h1
    omega
lemma applyInv_rowColConst {P N fixP fixN : Nat} {swapsP swapsN : List (Nat × Nat)}
    (hvP : invValid (2 ^ (P * N) - 1) fixP swapsP = true)
    (hvN : invValid (2 ^ (P * N) - 1) fixN swapsN = true)
    (hrP : rowInvOk P N fixP swapsP = true)
    (hcN : colInvOk P N fixN swapsN = true)
    {p n : Nat} (hrc : RowColConst P N p n) :
    RowColConst P N (applyInv fixP swapsP p) (applyInv fixN swapsN n) := by
  simp only [rowInvOk, colInvOk, Bool.and_eq_true, List.all_eq_true, Nat.beq_eq] at hrP hcN
  refine ⟨applyInv_lt hvP hrc.1, applyInv_lt hvN hrc.2.1, ?_, ?_⟩
  · intro i hi j hj
    have hfr := isRowConstMask_ok hrP.1 i hi j hj
    have hsw : ∀ q ∈ swapsP, (∀ i < P, ∀ j < N, q.1.testBit (i * N + j) = q.1.testBit (i * N)) ∧ q.2 % N = 0 ∧ q.1 < 2 ^ (P * N) := by
      intro q hq; have := hrP.2 q hq
      exact ⟨isRowConstMask_ok this.1, this.2, invValid_mem_lt hvP q hq⟩
    have hsr := swapList_rowConst ⟨hrc.1, hrc.2.2.1⟩ hsw i hi j hj
    simp only [applyInv, Nat.testBit_or, Nat.testBit_and, hrc.2.2.1 i hi j hj, hfr, hsr]
  · intro i hi j hj
    have hfc := isColConstMask_ok hcN.1 i hi j hj
    have hsw : ∀ q ∈ swapsN, (∀ i < P, ∀ j < N, q.1.testBit (i * N + j) = q.1.testBit j) ∧
        (∀ j < N, q.1.testBit j = true → j + q.2 < N) ∧ q.1 < 2 ^ (P * N) := by
      intro q hq; have h1 := hcN.2 q hq
      refine ⟨isColConstMask_ok h1.1, ?_, invValid_mem_lt hvN q hq⟩
      intro j' hj' hqj
      have h2 := h1.2 j' (List.mem_range.2 hj')
      simp [hqj] at h2; exact h2
    have hsc := swapList_colConst ⟨hrc.2.1, hrc.2.2.2⟩ hsw i hi j hj
    simp only [applyInv, Nat.testBit_or, Nat.testBit_and, hrc.2.2.2 i hi j hj, hfc, hsc]
structure W where
  p : Nat
  n : Nat
  t : Nat
  s : Nat
def W.toPNT (w : W) : Nat × Nat × Nat := (w.p, w.n, w.t)
def WOk (top : Nat) (ws : List W) : Prop := ∀ w ∈ ws, w.s = (w.p &&& (w.n ^^^ top))
lemma wOk_nil {top : Nat} : WOk top [] := fun _ h => by simp at h
lemma wOk_cons {top : Nat} {w : W} {ws : List W}
    (hw : w.s = (w.p &&& (w.n ^^^ top))) (hws : WOk top ws) : WOk top (w :: ws) := by
  intro x hx; rcases List.mem_cons.1 hx with rfl | hx
  · exact hw
  · exact hws x hx
lemma wOk_match {top : Nat} {b : Bool} {l1 l2 : List W} (h1 : WOk top l1) (h2 : WOk top l2) :
    WOk top (match b with | true => l1 | false => l2) := by
  cases b <;> assumption
lemma wOk_map_s {top : Nat} {ws : List W} (hok : WOk top ws) :
    ws.map W.s = (ws.map W.toPNT).map fun w => w.1 &&& (w.2.1 ^^^ top) := by
  induction ws with
  | nil => rfl
  | cons w rest ih =>
    simp only [List.map_cons, W.toPNT, hok w List.mem_cons_self,
      ih (fun x hx => hok x (List.mem_cons_of_mem _ hx))]
structure Cfg where
  top : Nat
  n1 : Nat
  n2 : Nat
  n4 : Nat
  n8 : Nat
  m1 : Nat
  m2 : Nat
  m4 : Nat
  m8 : Nat
  rs : Nat
  rf : Nat
  certHit : Nat → List W → Bool
def hasCrossW (c : Cfg) (u c2 : Nat) : List W → Nat → Bool
  | [], _ => false
  | w :: rest, r1 =>
    let s := w.s
    let uw := Nat.land u s
    match Nat.beq uw 0 with
    | true => hasCrossW c u c2 rest r1
    | false =>
      let sc := Nat.land s c2
      match Nat.beq sc 0 with
      | true => hasCrossW c u c2 rest r1
      | false =>
        let r := Nat.lor uw (Nat.land (Nat.shiftRight uw 1) c.m1)
        let r := Nat.lor r (Nat.land (Nat.shiftRight r 2) c.m2)
        let r := Nat.lor r (Nat.land (Nat.shiftRight r 4) c.m4)
        let r := Nat.land (Nat.lor r (Nat.land (Nat.shiftRight r 8) c.m8)) c.rs
        let rm := Nat.land sc (Nat.mul r c.rf)
        match Nat.beq rm 0 with
        | true => hasCrossW c u c2 rest r1
        | false =>
          let x := Nat.lor uw (Nat.shiftRight uw c.n8)
          let x := Nat.lor x (Nat.shiftRight x c.n4)
          let x := Nat.lor x (Nat.shiftRight x c.n2)
          let x := Nat.land (Nat.lor x (Nat.shiftRight x c.n1)) c.rf
          let cr := Nat.land rm (Nat.mul x c.rs)
          match Nat.beq (Nat.land r1 cr) 0 with
          | false => true
          | true => hasCrossW c u c2 rest (Nat.lor r1 cr)
lemma hasCrossW_eq (c : Cfg) (hn2 : c.n2 = 2 * c.n1) (hn4 : c.n4 = 4 * c.n1) (hn8 : c.n8 = 8 * c.n1)
    (u c2 : Nat) : ∀ (ws : List W) (r1 : Nat),
    hasCrossW c u c2 ws r1 = hasCrossAux c.m1 c.m2 c.m4 c.m8 c.rs c.n1 c.rf u c2 (ws.map W.s) r1 0
  | [], _ => rfl
  | w :: rest, r1 => by
    rw [List.map_cons]
    dsimp only [hasCrossW, hasCrossAux, rowMask, colMask]
    have hm2 : Nat.mul 2 c.n1 = c.n2 := hn2.symm
    have hm4 : Nat.mul 4 c.n1 = c.n4 := hn4.symm
    have hm8 : Nat.mul 8 c.n1 = c.n8 := hn8.symm
    rw [hm2, hm4, hm8]
    set uw := Nat.land u w.s
    cases Nat.beq uw 0
    · set sc := Nat.land w.s c2
      cases Nat.beq sc 0
      · set r := Nat.land (Nat.lor (Nat.lor (Nat.lor (Nat.lor uw (Nat.land (Nat.shiftRight uw 1) c.m1))
            (Nat.land (Nat.shiftRight (Nat.lor uw (Nat.land (Nat.shiftRight uw 1) c.m1)) 2) c.m2))
            (Nat.land (Nat.shiftRight (Nat.lor (Nat.lor uw (Nat.land (Nat.shiftRight uw 1) c.m1))
              (Nat.land (Nat.shiftRight (Nat.lor uw (Nat.land (Nat.shiftRight uw 1) c.m1)) 2) c.m2)) 4) c.m4))
            (Nat.land (Nat.shiftRight (Nat.lor (Nat.lor (Nat.lor uw (Nat.land (Nat.shiftRight uw 1) c.m1))
              (Nat.land (Nat.shiftRight (Nat.lor uw (Nat.land (Nat.shiftRight uw 1) c.m1)) 2) c.m2))
              (Nat.land (Nat.shiftRight (Nat.lor (Nat.lor uw (Nat.land (Nat.shiftRight uw 1) c.m1))
                (Nat.land (Nat.shiftRight (Nat.lor uw (Nat.land (Nat.shiftRight uw 1) c.m1)) 2) c.m2)) 4) c.m4)) 8) c.m8)) c.rs
        set rm := Nat.land sc (Nat.mul r c.rf)
        cases Nat.beq rm 0
        · set x := Nat.land (Nat.lor (Nat.lor (Nat.lor (Nat.lor uw (Nat.shiftRight uw c.n8))
              (Nat.shiftRight (Nat.lor uw (Nat.shiftRight uw c.n8)) c.n4))
              (Nat.shiftRight (Nat.lor (Nat.lor uw (Nat.shiftRight uw c.n8))
                (Nat.shiftRight (Nat.lor uw (Nat.shiftRight uw c.n8)) c.n4)) c.n2))
              (Nat.shiftRight (Nat.lor (Nat.lor (Nat.lor uw (Nat.shiftRight uw c.n8))
                (Nat.shiftRight (Nat.lor uw (Nat.shiftRight uw c.n8)) c.n4))
                (Nat.shiftRight (Nat.lor (Nat.lor uw (Nat.shiftRight uw c.n8))
                  (Nat.shiftRight (Nat.lor uw (Nat.shiftRight uw c.n8)) c.n4)) c.n2)) c.n1)) c.rf
          set cr := Nat.land rm (Nat.mul x c.rs)
          have h0 : Nat.lor 0 (Nat.land r1 cr) = Nat.land r1 cr := Nat.zero_or _
          rw [h0]
          cases h : Nat.beq (Nat.land r1 cr) 0
          · rfl
          · have heq : Nat.land r1 cr = 0 := Nat.eq_of_beq_eq_true h
            rw [heq]
            exact hasCrossW_eq c hn2 hn4 hn8 u c2 rest (Nat.lor r1 cr)
        · exact hasCrossW_eq c hn2 hn4 hn8 u c2 rest r1
      · exact hasCrossW_eq c hn2 hn4 hn8 u c2 rest r1
    · exact hasCrossW_eq c hn2 hn4 hn8 u c2 rest r1
def isDomW (gp gn : Nat) : List W → Bool
  | [] => false
  | w :: rest =>
    match Nat.beq (Nat.land gp w.p) gp with
    | true => match Nat.beq (Nat.land w.n gn) w.n with | true => true | false => isDomW gp gn rest
    | false => isDomW gp gn rest
def eraseO (pa na ta : Nat) : List W → List W → Option (List W)
  | [], _ => none
  | w :: rest, acc =>
    match Nat.beq w.p pa with
    | true => match Nat.beq w.n na with
      | true => match Nat.beq w.t ta with
        | true => some (revApp acc rest)
        | false => eraseO pa na ta rest (w :: acc)
      | false => eraseO pa na ta rest (w :: acc)
    | false => eraseO pa na ta rest (w :: acc)
def isPermW : List W → List W → Bool
  | [], [] => true
  | [], _ :: _ => false
  | w :: rest, ys => match eraseO w.p w.n w.t ys [] with
    | none => false
    | some ys' => isPermW rest ys'
lemma eraseO_sound {pa na ta : Nat} :
    ∀ (ys acc r : List W), eraseO pa na ta ys acc = some r →
      ((acc ++ ys).map W.toPNT).Perm ((pa, na, ta) :: r.map W.toPNT)
  | [], _, _, h => by simp [eraseO] at h
  | w :: rest, acc, r, h => by
    dsimp only [eraseO] at h
    have step_miss : eraseO pa na ta rest (w :: acc) = some r →
        ((acc ++ w :: rest).map W.toPNT).Perm ((pa, na, ta) :: r.map W.toPNT) := fun hm =>
      (List.perm_middle.map W.toPNT).trans (eraseO_sound rest (w :: acc) r hm)
    cases h1 : Nat.beq w.p pa <;> simp only [h1] at h
    · exact step_miss h
    · cases h2 : Nat.beq w.n na <;> simp only [h2] at h
      · exact step_miss h
      · cases h3 : Nat.beq w.t ta <;> simp only [h3] at h
        · exact step_miss h
        · cases h
          have hw : w.toPNT = (pa, na, ta) := by
            simp only [W.toPNT, Nat.eq_of_beq_eq_true h1, Nat.eq_of_beq_eq_true h2, Nat.eq_of_beq_eq_true h3]
          rw [← hw]
          exact (List.perm_middle.trans ((revApp_perm acc rest).symm.cons w)).map W.toPNT
lemma isPermW_sound {xs ys : List W} (h : isPermW xs ys = true) :
    (xs.map W.toPNT).Perm (ys.map W.toPNT) := by
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil => exact .nil
    | cons _ _ => simp [isPermW] at h
  | cons w rest ih =>
    dsimp only [isPermW] at h
    cases he : eraseO w.p w.n w.t ys [] with
    | none => simp [he] at h
    | some ys' =>
      simp only [he] at h
      have hp := eraseO_sound ys [] ys' he
      simp only [List.nil_append] at hp
      exact ((ih h).cons w.toPNT).trans hp.symm
structure CovR where
  c1 : Nat
  c2 : Nat
  len : Nat
def covPass : List W → Nat → Nat → Nat → CovR
  | [], c1, c2, len => ⟨c1, c2, len⟩
  | w :: rest, c1, c2, len =>
    let s := w.s
    covPass rest (Nat.lor c1 s) (Nat.lor c2 (Nat.land c1 s)) (Nat.add len 1)
lemma covPass_eq (top : Nat) : ∀ (ws : List W) (c1 c2 len : Nat), WOk top ws →
    covPass ws c1 c2 len =
    ⟨(buildSeps top (ws.map W.toPNT) c1 c2).2.1,
     (buildSeps top (ws.map W.toPNT) c1 c2).2.2,
     ws.length + len⟩
  | [], c1, c2, len, _ => by simp [covPass, buildSeps]
  | w :: rest, c1, c2, len, hok => by
    have hw := hok w List.mem_cons_self
    have hr : WOk top rest := fun x hx => hok x (List.mem_cons_of_mem _ hx)
    simp only [covPass, List.map_cons, W.toPNT, buildSeps, List.length_cons,
      nat_land_eq, nat_xor_eq, nat_lor_eq, nat_add_eq]
    rw [hw, covPass_eq top rest _ _ _ hr]
    congr 1; omega
def fastPairW (top : Nat) (v rest : List W) (a : W) (ua : Nat) (b : W) (ub : Nat) (cb : List W → Bool) : Bool :=
  let tryAnd : Bool :=
    match Nat.beq a.t 2 with
    | true => false
    | false => match Nat.beq b.t 2 with
      | true => false
      | false => match Nat.beq (Nat.land ua b.p) ua with
        | false => false
        | true => match Nat.beq (Nat.land ub a.p) ub with
          | false => false
          | true =>
            let gp := Nat.land a.p b.p
            match Nat.beq gp 0 with
            | true => false
            | false =>
              let gn := Nat.land a.n b.n
              match Nat.beq gn top with
              | true => false
              | false => match isDomW gp gn v with
                | true => false
                | false =>
                  let tg := match Nat.beq a.t 1 with | true => 2 | false => match Nat.beq b.t 1 with | true => 2 | false => 0
                  cb (⟨gp, gn, tg, Nat.land gp (Nat.xor gn top)⟩ :: rest)
  match tryAnd with
  | true => true
  | false =>
    match Nat.beq (Nat.land ua b.n) 0 with
    | false => false
    | true => match Nat.beq (Nat.land ub a.n) 0 with
      | false => false
      | true =>
        let gp := Nat.lor a.p b.p
        match Nat.beq gp 0 with
        | true => false
        | false =>
          let gn := Nat.lor a.n b.n
          match Nat.beq gn top with
          | true => false
          | false => match isDomW gp gn v with
            | true => false
            | false => cb (⟨gp, gn, 0, Nat.land gp (Nat.xor gn top)⟩ :: rest)
def slow1PairW (top : Nat) (v rest : List W) (a : W) (ua : Nat) (b : W) (ub : Nat) (cb : List W → Bool) : Bool :=
  let tryAnd : Bool :=
    match Nat.beq a.t 2 with
    | true => false
    | false => match Nat.beq b.t 2 with
      | true => false
      | false =>
        let da := Nat.beq (Nat.land ua b.p) ua
        let db := Nat.beq (Nat.land ub a.p) ub
        let ka := Nat.beq a.t 0
        let kb := Nat.beq b.t 0
        let ok := match da with | true => (match db with | true => true | false => kb) | false => (match db with | true => ka | false => false)
        match ok with
        | false => false
        | true =>
          let gp := Nat.land a.p b.p
          match Nat.beq gp 0 with
          | true => false
          | false =>
            let gn := Nat.land a.n b.n
            match Nat.beq gn top with
            | true => false
            | false => match isDomW gp gn v with
              | true => false
              | false =>
                let tg := match Nat.beq a.t 1 with | true => 2 | false => match Nat.beq b.t 1 with | true => 2 | false => 0
                let gw : W := ⟨gp, gn, tg, Nat.land gp (Nat.xor gn top)⟩
                let r1 := match da with | true => (match db with | true => cb (gw :: rest) | false => false) | false => false
                match r1 with
                | true => true
                | false =>
                  let r2 := match ka with | true => (match db with | true => cb (gw :: a :: rest) | false => false) | false => false
                  match r2 with
                  | true => true
                  | false => match da with | true => (match kb with | true => cb (gw :: b :: rest) | false => false) | false => false
  match tryAnd with
  | true => true
  | false =>
    let da := Nat.beq (Nat.land ua b.n) 0
    let db := Nat.beq (Nat.land ub a.n) 0
    let ka := match Nat.beq a.t 2 with | true => false | false => true
    let kb := match Nat.beq b.t 2 with | true => false | false => true
    let ok := match da with | true => (match db with | true => true | false => kb) | false => (match db with | true => ka | false => false)
    match ok with
    | false => false
    | true =>
      let gp := Nat.lor a.p b.p
      match Nat.beq gp 0 with
      | true => false
      | false =>
        let gn := Nat.lor a.n b.n
        match Nat.beq gn top with
        | true => false
        | false => match isDomW gp gn v with
          | true => false
          | false =>
            let gw : W := ⟨gp, gn, 0, Nat.land gp (Nat.xor gn top)⟩
            let r1 := match da with | true => (match db with | true => cb (gw :: rest) | false => false) | false => false
            match r1 with
            | true => true
            | false =>
              let r2 := match ka with | true => (match db with | true => cb (gw :: ⟨a.p, a.n, match Nat.beq a.t 1 with | true => 2 | false => a.t, a.s⟩ :: rest) | false => false) | false => false
              match r2 with
              | true => true
              | false => match da with | true => (match kb with | true => cb (gw :: ⟨b.p, b.n, match Nat.beq b.t 1 with | true => 2 | false => b.t, b.s⟩ :: rest) | false => false) | false => false
def slow2PairW (top : Nat) (v rest : List W) (a : W) (ua : Nat) (b : W) (ub : Nat) (cb : List W → Bool) : Bool :=
  let tryAnd : Bool :=
    match Nat.beq a.t 2 with
    | true => false
    | false => match Nat.beq b.t 2 with
      | true => false
      | false =>
        let da := Nat.beq (Nat.land ua b.p) ua
        let db := Nat.beq (Nat.land ub a.p) ub
        let ka := Nat.beq a.t 0
        let kb := Nat.beq b.t 0
        let okA := match da with | true => true | false => ka
        let okB := match db with | true => true | false => kb
        match okA with
        | false => false
        | true => match okB with
          | false => false
          | true =>
            let gp := Nat.land a.p b.p
            match Nat.beq gp 0 with
            | true => false
            | false =>
              let gn := Nat.land a.n b.n
              match Nat.beq gn top with
              | true => false
              | false => match isDomW gp gn v with
                | true => false
                | false =>
                  let tg := match Nat.beq a.t 1 with | true => 2 | false => match Nat.beq b.t 1 with | true => 2 | false => 0
                  let gw : W := ⟨gp, gn, tg, Nat.land gp (Nat.xor gn top)⟩
                  let r1 := match da with | true => (match db with | true => cb (gw :: rest) | false => false) | false => false
                  match r1 with
                  | true => true
                  | false =>
                    let r2 := match ka with | true => (match db with | true => cb (gw :: a :: rest) | false => false) | false => false
                    match r2 with
                    | true => true
                    | false =>
                      let r3 := match da with | true => (match kb with | true => cb (gw :: b :: rest) | false => false) | false => false
                      match r3 with
                      | true => true
                      | false => match ka with | true => (match kb with | true => cb (gw :: a :: b :: rest) | false => false) | false => false
  match tryAnd with
  | true => true
  | false =>
    let da := Nat.beq (Nat.land ua b.n) 0
    let db := Nat.beq (Nat.land ub a.n) 0
    let ka := match Nat.beq a.t 2 with | true => false | false => true
    let kb := match Nat.beq b.t 2 with | true => false | false => true
    let okA := match da with | true => true | false => ka
    let okB := match db with | true => true | false => kb
    match okA with
    | false => false
    | true => match okB with
      | false => false
      | true =>
        let gp := Nat.lor a.p b.p
        match Nat.beq gp 0 with
        | true => false
        | false =>
          let gn := Nat.lor a.n b.n
          match Nat.beq gn top with
          | true => false
          | false => match isDomW gp gn v with
            | true => false
            | false =>
              let gw : W := ⟨gp, gn, 0, Nat.land gp (Nat.xor gn top)⟩
              let a' : W := ⟨a.p, a.n, match Nat.beq a.t 1 with | true => 2 | false => a.t, a.s⟩
              let b' : W := ⟨b.p, b.n, match Nat.beq b.t 1 with | true => 2 | false => b.t, b.s⟩
              let r1 := match da with | true => (match db with | true => cb (gw :: rest) | false => false) | false => false
              match r1 with
              | true => true
              | false =>
                let r2 := match ka with | true => (match db with | true => cb (gw :: a' :: rest) | false => false) | false => false
                match r2 with
                | true => true
                | false =>
                  let r3 := match da with | true => (match kb with | true => cb (gw :: b' :: rest) | false => false) | false => false
                  match r3 with
                  | true => true
                  | false => match ka with | true => (match kb with | true => cb (gw :: a' :: b' :: rest) | false => false) | false => false
def scanFastOneW (top u : Nat) (v : List W) (a : W) (ua : Nat) (cb : List W → Bool) : List W → List W → Bool
  | pre, b :: ws =>
    match fastPairW top v (revApp pre ws) a ua b (Nat.land u b.s) cb with
    | true => true
    | false => scanFastOneW top u v a ua cb (b :: pre) ws
  | _, [] => false
def scanFastW (top u : Nat) (v : List W) (cb : List W → Bool) : List W → List W → Bool
  | pre, a :: ws =>
    match scanFastOneW top u v a (Nat.land u a.s) cb pre ws with
    | true => true
    | false => scanFastW top u v cb (a :: pre) ws
  | _, [] => false
def scanSlow1OneW (top u : Nat) (v : List W) (a : W) (ua : Nat) (cb : List W → Bool) : List W → List W → Bool
  | pre, b :: ws =>
    match slow1PairW top v (revApp pre ws) a ua b (Nat.land u b.s) cb with
    | true => true
    | false => scanSlow1OneW top u v a ua cb (b :: pre) ws
  | _, [] => false
def scanSlow1W (top u : Nat) (v : List W) (cb : List W → Bool) : List W → List W → Bool
  | pre, a :: ws =>
    match scanSlow1OneW top u v a (Nat.land u a.s) cb pre ws with
    | true => true
    | false => scanSlow1W top u v cb (a :: pre) ws
  | _, [] => false
def scanSlow2OneW (top u : Nat) (v : List W) (a : W) (ua : Nat) (cb : List W → Bool) : List W → List W → Bool
  | pre, b :: ws =>
    match slow2PairW top v (revApp pre ws) a ua b (Nat.land u b.s) cb with
    | true => true
    | false => scanSlow2OneW top u v a ua cb (b :: pre) ws
  | _, [] => false
def scanSlow2W (top u : Nat) (v : List W) (cb : List W → Bool) : List W → List W → Bool
  | pre, a :: ws =>
    match scanSlow2OneW top u v a (Nat.land u a.s) cb pre ws with
    | true => true
    | false => scanSlow2W top u v cb (a :: pre) ws
  | _, [] => false
def searchCertW (c : Cfg) : Nat → List W → Bool
  | 0, [w] => match Nat.beq w.p c.top with | true => Nat.beq w.n 0 | false => false
  | 0, _ => false
  | k + 1, [w] => match Nat.beq w.p c.top with | true => Nat.beq w.n 0 | false => false
  | k + 1, v =>
    let r := covPass v 0 0 0
    match Nat.ble (Nat.add k 3) r.len with
    | true => false
    | false => match Nat.beq r.c1 c.top with
      | false => false
      | true =>
        let u := Nat.xor r.c1 r.c2
        let tight := Nat.beq r.len (Nat.add k 2)
        let killed := match tight with
          | true => hasCrossW c u r.c2 v 0
          | false => false
        match killed with
        | true => false
        | false => match c.certHit (Nat.add k 1) v with
          | true => false
          | false =>
            let cb := searchCertW c k
            match tight with
            | true => scanFastW c.top u v cb [] v
            | false => match Nat.beq r.len (Nat.add k 1) with
              | true => scanSlow1W c.top u v cb [] v
              | false => scanSlow2W c.top u v cb [] v
def searchCert (top N m1 m2 m4 m8 rowStart rowFull : Nat)
    (certHit : Nat → List W → Bool) (k : Nat) (v : List W) : Bool :=
  searchCertW ⟨top, N, Nat.mul 2 N, Nat.mul 4 N, Nat.mul 8 N, m1, m2, m4, m8, rowStart, rowFull, certHit⟩ k v
def stepExpand (top N m1 m2 m4 m8 rowStart rowFull : Nat)
    (certHit : Nat → List W → Bool) : Nat → List W → Bool
  | 0, [w] => match Nat.beq w.p top with | true => Nat.beq w.n 0 | false => false
  | 0, _ => false
  | k + 1, [w] => match Nat.beq w.p top with | true => Nat.beq w.n 0 | false => false
  | k + 1, v =>
    let c : Cfg := ⟨top, N, Nat.mul 2 N, Nat.mul 4 N, Nat.mul 8 N, m1, m2, m4, m8, rowStart, rowFull, certHit⟩
    let r := covPass v 0 0 0
    match Nat.ble (Nat.add k 3) r.len with
    | true => false
    | false => match Nat.beq r.c1 top with
      | false => false
      | true =>
        let u := Nat.xor r.c1 r.c2
        let tight := Nat.beq r.len (Nat.add k 2)
        let killed := match tight with
          | true => hasCrossW c u r.c2 v 0
          | false => false
        match killed with
        | true => false
        | false =>
          let cb := searchCertW c k
          match tight with
          | true => scanFastW top u v cb [] v
          | false => match Nat.beq r.len (Nat.add k 1) with
            | true => scanSlow1W top u v cb [] v
            | false => scanSlow2W top u v cb [] v
def HasOrderedPair {α : Type} (a b : α) : List α → Prop
  | [] => False
  | x :: rest => (x = a ∧ b ∈ rest) ∨ HasOrderedPair a b rest
lemma perm_hasOrderedPair {α : Type} {a b : α} {ws rest : List α}
    (hp : ws.Perm (a :: b :: rest)) : HasOrderedPair a b ws ∨ HasOrderedPair b a ws := by
  induction ws generalizing rest with
  | nil => have := hp.length_eq; simp at this
  | cons x t ih =>
    by_cases hxa : x = a
    · subst hxa
      have hb : b ∈ t := (hp.cons_inv).mem_iff.2 List.mem_cons_self
      exact Or.inl (Or.inl ⟨rfl, hb⟩)
    · by_cases hxb : x = b
      · subst hxb
        have ha : a ∈ t := ((hp.trans (List.Perm.swap _ _ _)).cons_inv).mem_iff.2 List.mem_cons_self
        exact Or.inr (Or.inl ⟨rfl, ha⟩)
      · have hxm : x ∈ a :: b :: rest := hp.mem_iff.1 List.mem_cons_self
        rcases List.mem_cons.1 hxm with rfl | hxm
        · exact absurd rfl hxa
        · rcases List.mem_cons.1 hxm with rfl | hxr
          · exact absurd rfl hxb
          · classical
            have h1 : (a :: b :: rest).Perm (x :: a :: b :: rest.erase x) :=
              (((List.perm_cons_erase hxr).cons b).cons a).trans
                (((List.Perm.swap _ _ _).cons a).trans (List.Perm.swap _ _ _))
            have hpt : t.Perm (a :: b :: rest.erase x) := (hp.trans h1).cons_inv
            rcases ih hpt with h | h
            · exact Or.inl (Or.inr h)
            · exact Or.inr (Or.inr h)
lemma scanFastOneW_of_mem {top u : Nat} {v : List W} {a b : W} {ua : Nat}
    {cb : List W → Bool} {pre ws : List W} (hm : b ∈ ws)
    (h : ∀ r, (pre ++ ws).Perm (b :: r) → fastPairW top v r a ua b (u &&& b.s) cb = true) :
    scanFastOneW top u v a ua cb pre ws = true := by
  induction ws generalizing pre with
  | nil => simp at hm
  | cons x t ih =>
    simp only [scanFastOneW, nat_land_eq]
    rcases List.mem_cons.1 hm with rfl | ht
    · rw [h _ (List.perm_middle.trans ((revApp_perm pre t).symm.cons b))]
    · cases hf : fastPairW top v (revApp pre t) a ua x (u &&& x.s) cb
      · exact ih ht (fun r hr => h r (List.perm_middle.trans hr))
      · rfl
lemma scanFastW_of_pair {top u : Nat} {v : List W} {a b : W} {cb : List W → Bool}
    {pre ws : List W} (hp : HasOrderedPair a b ws)
    (h : ∀ r, (pre ++ ws).Perm (a :: b :: r) → fastPairW top v r a (u &&& a.s) b (u &&& b.s) cb = true) :
    scanFastW top u v cb pre ws = true := by
  induction ws generalizing pre with
  | nil => exact False.elim hp
  | cons x t ih =>
    simp only [scanFastW, nat_land_eq]
    rcases hp with ⟨rfl, hb⟩ | hrest
    · rw [scanFastOneW_of_mem hb (fun r hr => h r (List.perm_middle.trans (hr.cons x)))]
    · cases h1 : scanFastOneW top u v x (u &&& x.s) cb pre t
      · exact ih hrest (fun r hr => h r (List.perm_middle.trans hr))
      · rfl
lemma scanSlow1OneW_of_mem {top u : Nat} {v : List W} {a b : W} {ua : Nat}
    {cb : List W → Bool} {pre ws : List W} (hm : b ∈ ws)
    (h : ∀ r, (pre ++ ws).Perm (b :: r) → slow1PairW top v r a ua b (u &&& b.s) cb = true) :
    scanSlow1OneW top u v a ua cb pre ws = true := by
  induction ws generalizing pre with
  | nil => simp at hm
  | cons x t ih =>
    simp only [scanSlow1OneW, nat_land_eq]
    rcases List.mem_cons.1 hm with rfl | ht
    · rw [h _ (List.perm_middle.trans ((revApp_perm pre t).symm.cons b))]
    · cases hf : slow1PairW top v (revApp pre t) a ua x (u &&& x.s) cb
      · exact ih ht (fun r hr => h r (List.perm_middle.trans hr))
      · rfl
lemma scanSlow1W_of_pair {top u : Nat} {v : List W} {a b : W} {cb : List W → Bool}
    {pre ws : List W} (hp : HasOrderedPair a b ws)
    (h : ∀ r, (pre ++ ws).Perm (a :: b :: r) → slow1PairW top v r a (u &&& a.s) b (u &&& b.s) cb = true) :
    scanSlow1W top u v cb pre ws = true := by
  induction ws generalizing pre with
  | nil => exact False.elim hp
  | cons x t ih =>
    simp only [scanSlow1W, nat_land_eq]
    rcases hp with ⟨rfl, hb⟩ | hrest
    · rw [scanSlow1OneW_of_mem hb (fun r hr => h r (List.perm_middle.trans (hr.cons x)))]
    · cases h1 : scanSlow1OneW top u v x (u &&& x.s) cb pre t
      · exact ih hrest (fun r hr => h r (List.perm_middle.trans hr))
      · rfl
lemma scanSlow2OneW_of_mem {top u : Nat} {v : List W} {a b : W} {ua : Nat}
    {cb : List W → Bool} {pre ws : List W} (hm : b ∈ ws)
    (h : ∀ r, (pre ++ ws).Perm (b :: r) → slow2PairW top v r a ua b (u &&& b.s) cb = true) :
    scanSlow2OneW top u v a ua cb pre ws = true := by
  induction ws generalizing pre with
  | nil => simp at hm
  | cons x t ih =>
    simp only [scanSlow2OneW, nat_land_eq]
    rcases List.mem_cons.1 hm with rfl | ht
    · rw [h _ (List.perm_middle.trans ((revApp_perm pre t).symm.cons b))]
    · cases hf : slow2PairW top v (revApp pre t) a ua x (u &&& x.s) cb
      · exact ih ht (fun r hr => h r (List.perm_middle.trans hr))
      · rfl
lemma scanSlow2W_of_pair {top u : Nat} {v : List W} {a b : W} {cb : List W → Bool}
    {pre ws : List W} (hp : HasOrderedPair a b ws)
    (h : ∀ r, (pre ++ ws).Perm (a :: b :: r) → slow2PairW top v r a (u &&& a.s) b (u &&& b.s) cb = true) :
    scanSlow2W top u v cb pre ws = true := by
  induction ws generalizing pre with
  | nil => exact False.elim hp
  | cons x t ih =>
    simp only [scanSlow2W, nat_land_eq]
    rcases hp with ⟨rfl, hb⟩ | hrest
    · rw [scanSlow2OneW_of_mem hb (fun r hr => h r (List.perm_middle.trans (hr.cons x)))]
    · cases h1 : scanSlow2OneW top u v x (u &&& x.s) cb pre t
      · exact ih hrest (fun r hr => h r (List.perm_middle.trans hr))
      · rfl
lemma isDomW_false_of_all {gp gn : Nat} {ws : List W}
    (h : ∀ w ∈ ws, ¬ ((gp &&& w.p) = gp ∧ (w.n &&& gn) = w.n)) :
    isDomW gp gn ws = false := by
  induction ws with
  | nil => rfl
  | cons w t ih =>
    have hw := h w List.mem_cons_self
    have ht := ih (fun w' hw' => h w' (List.mem_cons_of_mem _ hw'))
    simp only [isDomW, nat_land_eq]
    cases h1 : Nat.beq (gp &&& w.p) gp
    · exact ht
    · cases h2 : Nat.beq (w.n &&& gn) w.n
      · exact ht
      · exact absurd ⟨Nat.eq_of_beq_eq_true h1, Nat.eq_of_beq_eq_true h2⟩ hw
lemma drop_cond_ok {M k : Nat} {ws rest : List (Nat × Nat × Nat)}
    {pa na ta pb nb tb : Nat} {isOr kb : Bool}
    (hrc : ∀ w ∈ ws, w.1 < 2 ^ M ∧ w.2.1 < 2 ^ M)
    (hp : ws.Perm ((pa, na, ta) :: (pb, nb, tb) :: rest))
    (hrec : NatTRestricted (2 ^ M - 1) k
      ((if isOr then (pa ||| pb) else (pa &&& pb),
        if isOr then (na ||| nb) else (na &&& nb),
        if !isOr && (Nat.beq ta 1 || Nat.beq tb 1) then 2 else 0) ::
       kept false (pa, na, if isOr && Nat.beq ta 1 then 2 else ta)
         (kept kb (pb, nb, if isOr && Nat.beq tb 1 then 2 else tb) rest))) :
    let top := 2 ^ M - 1
    let u := (buildSeps top ws 0 0).2.1 ^^^ (buildSeps top ws 0 0).2.2
    let ua := u &&& (pa &&& (na ^^^ top))
    (if isOr then (ua &&& nb) = 0 else (ua &&& pb) = ua) := by
  set top := 2 ^ M - 1
  set u := (buildSeps top ws 0 0).2.1 ^^^ (buildSeps top ws 0 0).2.2
  set ua := u &&& (pa &&& (na ^^^ top))
  have ha_lt := hrc (pa, na, ta) (hp.mem_iff.2 List.mem_cons_self)
  have hb_lt := hrc (pb, nb, tb) (hp.mem_iff.2 (List.mem_cons_of_mem _ List.mem_cons_self))
  have hlt' : ∀ w ∈ (if isOr then (pa ||| pb) else (pa &&& pb),
      if isOr then (na ||| nb) else (na &&& nb),
      if !isOr && (Nat.beq ta 1 || Nat.beq tb 1) then 2 else 0) ::
      kept kb (pb, nb, if isOr && Nat.beq tb 1 then 2 else tb) rest, w.1 < 2 ^ M := by
    intro w hw; rcases List.mem_cons.1 hw with rfl | hw
    · cases isOr
      · exact Nat.lt_of_le_of_lt Nat.and_le_left ha_lt.1
      · exact Nat.or_lt_two_pow ha_lt.1 hb_lt.1
    · cases kb <;> simp only [kept, ite_true, ite_false, Bool.false_eq_true, List.mem_cons] at hw
      · exact (hrc w (hp.mem_iff.2 (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hw)))).1
      · rcases hw with rfl | hw
        · exact hb_lt.1
        · exact (hrc w (hp.mem_iff.2 (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hw)))).1
  simp only [kept, Bool.false_eq_true, ite_false] at hrec
  have hcov := natTRestricted_sepsOr k _ hlt' hrec
  cases isOr
  · simp only [Bool.false_eq_true, ite_false] at hcov ⊢
    apply Nat.eq_of_testBit_eq; intro idx
    rw [Nat.testBit_and]
    cases hua : ua.testBit idx
    · simp
    · simp only [Bool.true_and]
      have huas := hua
      simp only [ua, Nat.testBit_and, Bool.and_eq_true] at huas
      have hidx_lt : idx < M := by
        by_contra hge; push Not at hge
        have h0 := Nat.testBit_eq_false_of_lt (Nat.lt_of_lt_of_le ha_lt.1 (Nat.pow_le_pow_right (by omega) hge))
        rw [huas.2.1] at h0; contradiction
      have hsep_a : (pa &&& (na ^^^ top)).testBit idx = true := by rw [Nat.testBit_and, huas.2.1, huas.2.2]; rfl
      have hno := unique_sep_no_other top hp idx huas.1 hsep_a
      have hcov_i := congrArg (fun z => z.testBit idx) hcov
      simp only [top, Nat.testBit_two_pow_sub_one, decide_eq_true hidx_lt] at hcov_i
      simp only [sepsOr, Nat.testBit_or, Bool.or_eq_true] at hcov_i
      have htail_f : (sepsOr top (kept kb (pb, nb, if false && Nat.beq tb 1 then 2 else tb) rest)).testBit idx = false := by
        have hall : ∀ l : List (Nat × Nat × Nat), (∀ w ∈ l, (w.1 &&& (w.2.1 ^^^ top)).testBit idx = false) → (sepsOr top l).testBit idx = false := by
          intro l hl; induction l with
          | nil => simp [sepsOr]
          | cons w t iht =>
            rcases w with ⟨p, n, tg⟩
            simp [sepsOr, Nat.testBit_or, hl _ List.mem_cons_self, iht (fun w' hw' => hl w' (List.mem_cons_of_mem _ hw'))]
        apply hall; intro w hw
        cases kb <;> simp only [kept, ite_true, ite_false, Bool.false_eq_true, List.mem_cons] at hw
        · exact hno w (List.mem_cons_of_mem _ hw)
        · rcases hw with rfl | hw
          · exact hno (pb, nb, tb) List.mem_cons_self
          · exact hno w (List.mem_cons_of_mem _ hw)
      dsimp only [top] at htail_f
      simp only [htail_f, Bool.false_eq_true, or_false] at hcov_i
      simp only [Nat.testBit_and, Bool.and_eq_true] at hcov_i
      exact hcov_i.1.2
  · simp only [ite_true] at hcov ⊢
    apply Nat.eq_of_testBit_eq; intro idx
    rw [Nat.testBit_and, Nat.zero_testBit]
    cases hua : ua.testBit idx
    · simp
    · simp only [Bool.true_and]
      have huas := hua
      simp only [ua, Nat.testBit_and, Bool.and_eq_true] at huas
      have hidx_lt : idx < M := by
        by_contra hge; push Not at hge
        have h0 := Nat.testBit_eq_false_of_lt (Nat.lt_of_lt_of_le ha_lt.1 (Nat.pow_le_pow_right (by omega) hge))
        rw [huas.2.1] at h0; contradiction
      have hsep_a : (pa &&& (na ^^^ top)).testBit idx = true := by rw [Nat.testBit_and, huas.2.1, huas.2.2]; rfl
      have hno := unique_sep_no_other top hp idx huas.1 hsep_a
      have hcov_i := congrArg (fun z => z.testBit idx) hcov
      simp only [top, Nat.testBit_two_pow_sub_one, decide_eq_true hidx_lt] at hcov_i
      simp only [sepsOr, Nat.testBit_or, Bool.or_eq_true] at hcov_i
      have htail_f : (sepsOr top (kept kb (pb, nb, if true && Nat.beq tb 1 then 2 else tb) rest)).testBit idx = false := by
        have hall : ∀ l : List (Nat × Nat × Nat), (∀ w ∈ l, (w.1 &&& (w.2.1 ^^^ top)).testBit idx = false) → (sepsOr top l).testBit idx = false := by
          intro l hl; induction l with
          | nil => simp [sepsOr]
          | cons w t iht =>
            rcases w with ⟨p, n, tg⟩
            simp [sepsOr, Nat.testBit_or, hl _ List.mem_cons_self, iht (fun w' hw' => hl w' (List.mem_cons_of_mem _ hw'))]
        apply hall; intro w hw
        cases kb <;> simp only [kept, ite_true, ite_false, Bool.false_eq_true, List.mem_cons] at hw
        · exact hno w (List.mem_cons_of_mem _ hw)
        · rcases hw with rfl | hw
          · exact hno (pb, nb, tb) List.mem_cons_self
          · exact hno w (List.mem_cons_of_mem _ hw)
      dsimp only [top] at htail_f
      simp only [htail_f, Bool.false_eq_true, or_false] at hcov_i
      simp only [top, Nat.testBit_and, Nat.testBit_xor, Nat.testBit_or, Nat.testBit_two_pow_sub_one,
        decide_eq_true hidx_lt, Bool.and_eq_true] at hcov_i
      cases hnb : nb.testBit idx
      · rfl
      · simp [hnb] at hcov_i
private lemma tg_match_eq (ta tb : Nat) :
    (match Nat.beq ta 1 with | true => 2 | false => match Nat.beq tb 1 with | true => 2 | false => 0) =
    (if Nat.beq ta 1 || Nat.beq tb 1 then 2 else 0) := by
  cases Nat.beq ta 1 <;> cases Nat.beq tb 1 <;> rfl
private lemma ta_match_eq (t : Nat) :
    (match Nat.beq t 1 with | true => 2 | false => t) =
    (if Nat.beq t 1 then 2 else t) := by
  cases Nat.beq t 1 <;> rfl
private lemma match_or_true_left {a b : Bool} :
    a = true → (match a with | true => true | false => b) = true := by intro h; subst h; rfl
private lemma match_or_true_right {a b : Bool} :
    b = true → (match a with | true => true | false => b) = true := by intro h; cases a <;> simp [h]
private lemma match_bool_const {α : Type} (b : Bool) (x : α) :
    (match b with | true => x | false => x) = x := by cases b <;> rfl
lemma step_body_completeW {P N m1 m2 m4 m8 rowStart rowFull k : Nat}
    {ws : List W} {cb : List W → Bool}
    (hN : 0 < N) (hrf : rowFull = (1 <<< N) - 1) (hrs : RowStartOk P N rowStart)
    (hm1 : MaskLoOk P N 1 m1) (hm2 : MaskLoOk P N 2 m2)
    (hm4 : MaskLoOk P N 4 m4) (hm8 : MaskLoOk P N 8 m8)
    (hok : WOk (2 ^ (P * N) - 1) ws)
    (hrc : ∀ w ∈ ws.map W.toPNT, RowColConst P N w.1 w.2.1)
    (h : NatTRestricted (2 ^ (P * N) - 1) (k + 1) (ws.map W.toPNT))
    (hcb : ∀ zs, WOk (2 ^ (P * N) - 1) zs → (∀ w ∈ zs.map W.toPNT, RowColConst P N w.1 w.2.1) →
      NatTRestricted (2 ^ (P * N) - 1) k (zs.map W.toPNT) → cb zs = true) :
    let top := 2 ^ (P * N) - 1
    let c1 := (buildSeps top (ws.map W.toPNT) 0 0).2.1
    let c2 := (buildSeps top (ws.map W.toPNT) 0 0).2.2
    let u := c1 ^^^ c2
    ws.length < k + 3 ∧ c1 = top ∧
    (ws.length = k + 2 → hasCrossAux m1 m2 m4 m8 rowStart N rowFull u c2 (ws.map W.s) 0 0 = false) ∧
    (match Nat.beq ws.length (k + 2) with
     | true => scanFastW top u ws cb [] ws
     | false => match Nat.beq ws.length (k + 1) with
       | true => scanSlow1W top u ws cb [] ws
       | false => scanSlow2W top u ws cb [] ws) = true := by
  set top := 2 ^ (P * N) - 1
  set pnts := ws.map W.toPNT
  have hlen_eq : pnts.length = ws.length := List.length_map _
  have hlen_le := natTRestricted_len (k + 1) pnts h
  have hlt_lt : ∀ w ∈ pnts, w.1 < 2 ^ (P * N) ∧ w.2.1 < 2 ^ (P * N) := fun w hw => ⟨(hrc w hw).1, (hrc w hw).2.1⟩
  have hc1_eq : (buildSeps top pnts 0 0).2.1 = top := by
    rw [buildSeps_c1, Nat.zero_or]
    exact natTRestricted_sepsOr (k + 1) pnts (fun w hw => (hlt_lt w hw).1) h
  have hcross_ok : ws.length = k + 2 →
      hasCrossAux m1 m2 m4 m8 rowStart N rowFull
        ((buildSeps top pnts 0 0).2.1 ^^^ (buildSeps top pnts 0 0).2.2)
        (buildSeps top pnts 0 0).2.2 (ws.map W.s) 0 0 = false := by
    intro hl
    rw [wOk_map_s hok]
    exact natTRestricted_no_cross hN hrf hrs hm1 hm2 hm4 hm8 hrc h (by omega)
  refine ⟨by omega, hc1_eq, hcross_ok, ?_⟩
  obtain ⟨pa0, na0, ta0, pb0, nb0, tb0, rest0, isOr, ka0, kb0, hp0, h10, h20, h30, hgp0, hgn0, hdom0, hrec0⟩ := h
  obtain ⟨l', hlp0, hlm0⟩ := perm_map_exists W.toPNT hp0
  cases l' with
  | nil => simp at hlm0
  | cons wa0 l1 =>
    cases l1 with
    | nil => simp at hlm0
    | cons wb0 wrest0 =>
      simp only [List.map_cons, List.cons.injEq] at hlm0
      obtain ⟨hwa0, hwb0, hwrest0⟩ := hlm0
      have hwa0_eq : wa0.p = pa0 ∧ wa0.n = na0 ∧ wa0.t = ta0 := by
        simpa [W.toPNT] using hwa0
      have hwb0_eq : wb0.p = pb0 ∧ wb0.n = nb0 ∧ wb0.t = tb0 := by
        simpa [W.toPNT] using hwb0
      have horient : ∃ (wa wb : W) (ka kb : Bool),
          ws.Perm (wa :: wb :: wrest0) ∧
          HasOrderedPair wa wb ws ∧
          (isOr = true ∨ (wa.t ≠ 2 ∧ wb.t ≠ 2)) ∧
          (ka = false ∨ (if isOr then wa.t ≠ 2 else wa.t = 0)) ∧
          (kb = false ∨ (if isOr then wb.t ≠ 2 else wb.t = 0)) ∧
          let gp := if isOr then (wa.p ||| wb.p) else (wa.p &&& wb.p)
          let gn := if isOr then (wa.n ||| wb.n) else (wa.n &&& wb.n)
          gp ≠ 0 ∧ gn ≠ top ∧
          (∀ w ∈ pnts, ¬ ((gp &&& w.1) = gp ∧ (w.2.1 &&& gn) = w.2.1)) ∧
          let tg := if !isOr && (Nat.beq wa.t 1 || Nat.beq wb.t 1) then 2 else 0
          let ta' := if isOr && Nat.beq wa.t 1 then 2 else wa.t
          let tb' := if isOr && Nat.beq wb.t 1 then 2 else wb.t
          NatTRestricted top k ((gp, gn, tg) :: kept ka (wa.p, wa.n, ta') (kept kb (wb.p, wb.n, tb') rest0)) := by
        rcases perm_hasOrderedPair hlp0 with hord | hord
        · refine ⟨wa0, wb0, ka0, kb0, hlp0, hord, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
          all_goals simp only [hwa0_eq.1, hwa0_eq.2.1, hwa0_eq.2.2, hwb0_eq.1, hwb0_eq.2.1, hwb0_eq.2.2]
          · exact h10
          · exact h20
          · exact h30
          · exact hgp0
          · exact hgn0
          · exact hdom0
          · exact hrec0
        · refine ⟨wb0, wa0, kb0, ka0, hlp0.trans (List.Perm.swap _ _ _), hord, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
          all_goals simp only [hwa0_eq.1, hwa0_eq.2.1, hwa0_eq.2.2, hwb0_eq.1, hwb0_eq.2.1, hwb0_eq.2.2]
          · exact h10.imp id (fun ⟨a, b⟩ => ⟨b, a⟩)
          · exact h30
          · exact h20
          · cases isOr <;> simp only [ite_true, ite_false, Bool.false_eq_true] at hgp0 ⊢
            · rwa [Nat.and_comm]
            · rwa [Nat.or_comm]
          · cases isOr <;> simp only [ite_true, ite_false, Bool.false_eq_true] at hgn0 ⊢
            · rwa [Nat.and_comm]
            · rwa [Nat.or_comm]
          · cases isOr <;> simp only [ite_true, ite_false, Bool.false_eq_true] at hdom0 ⊢
            · simpa [Nat.and_comm] using hdom0
            · simpa [Nat.or_comm] using hdom0
          · have hcomm_p : (if isOr then pb0 ||| pa0 else pb0 &&& pa0) = (if isOr then pa0 ||| pb0 else pa0 &&& pb0) := by
              cases isOr <;> simp [Nat.and_comm, Nat.or_comm]
            have hcomm_n : (if isOr then nb0 ||| na0 else nb0 &&& na0) = (if isOr then na0 ||| nb0 else na0 &&& nb0) := by
              cases isOr <;> simp [Nat.and_comm, Nat.or_comm]
            have hcomm_t : (if !isOr && (Nat.beq tb0 1 || Nat.beq ta0 1) then 2 else 0) =
                (if !isOr && (Nat.beq ta0 1 || Nat.beq tb0 1) then 2 else 0) := by
              rw [Bool.or_comm]
            rw [hcomm_p, hcomm_n, hcomm_t]
            apply natTRestricted_perm _ hrec0
            apply List.Perm.cons
            cases ka0 <;> cases kb0 <;> simp only [kept, ite_true, ite_false, Bool.false_eq_true]
            · exact List.Perm.refl _
            · exact List.Perm.refl _
            · exact List.Perm.refl _
            · exact List.Perm.swap _ _ _
      obtain ⟨wa, wb, ka, kb, hpW, hord, h1, h2, h3, hgp, hgn, hdom, hrec⟩ := horient
      have hp : pnts.Perm ((wa.p, wa.n, wa.t) :: (wb.p, wb.n, wb.t) :: rest0) := by
        simpa [pnts, W.toPNT, hwrest0] using hpW.map W.toPNT
      set u := (buildSeps top pnts 0 0).2.1 ^^^ (buildSeps top pnts 0 0).2.2
      have hwas : wa.s = (wa.p &&& (wa.n ^^^ top)) := hok wa (hpW.mem_iff.2 List.mem_cons_self)
      have hwbs : wb.s = (wb.p &&& (wb.n ^^^ top)) := hok wb (hpW.mem_iff.2 (List.mem_cons_of_mem _ List.mem_cons_self))
      set gp := if isOr then (wa.p ||| wb.p) else (wa.p &&& wb.p)
      set gn := if isOr then (wa.n ||| wb.n) else (wa.n &&& wb.n)
      set tg := if !isOr && (Nat.beq wa.t 1 || Nat.beq wb.t 1) then 2 else 0
      set ta' := if isOr && Nat.beq wa.t 1 then 2 else wa.t
      set tb' := if isOr && Nat.beq wb.t 1 then 2 else wb.t
      have hrc_a := hrc (wa.p, wa.n, wa.t) (hp.mem_iff.2 List.mem_cons_self)
      have hrc_b := hrc (wb.p, wb.n, wb.t) (hp.mem_iff.2 (List.mem_cons_of_mem _ List.mem_cons_self))
      have hrc_g : RowColConst P N gp gn := by
        cases isOr
        · exact rowColConst_and hrc_a hrc_b
        · exact rowColConst_or hrc_a hrc_b
      have hcb_any : ∀ r : List W, ([] ++ ws).Perm (wa :: wb :: r) →
          cb (⟨gp, gn, tg, gp &&& (gn ^^^ top)⟩ ::
            kept ka ⟨wa.p, wa.n, ta', wa.s⟩ (kept kb ⟨wb.p, wb.n, tb', wb.s⟩ r)) = true := by
        intro r hr
        have hws_r : ws.Perm (wa :: wb :: r) := by simpa using hr
        have hrrW : wrest0.Perm r := (hpW.symm.trans hws_r).cons_inv.cons_inv
        have hrr : rest0.Perm (r.map W.toPNT) := by rw [← hwrest0]; exact hrrW.map W.toPNT
        set child : List W := ⟨gp, gn, tg, gp &&& (gn ^^^ top)⟩ ::
            kept ka ⟨wa.p, wa.n, ta', wa.s⟩ (kept kb ⟨wb.p, wb.n, tb', wb.s⟩ r)
        have hok_child : WOk top child := by
          intro w hw
          rcases List.mem_cons.1 hw with rfl | hw
          · rfl
          · cases ka <;> cases kb <;> simp only [kept, ite_true, ite_false, Bool.false_eq_true, List.mem_cons] at hw
            · exact hok w (hws_r.mem_iff.2 (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hw)))
            · rcases hw with rfl | hw
              · exact hwbs
              · exact hok w (hws_r.mem_iff.2 (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hw)))
            · rcases hw with rfl | hw
              · exact hwas
              · exact hok w (hws_r.mem_iff.2 (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hw)))
            · rcases hw with rfl | rfl | hw
              · exact hwas
              · exact hwbs
              · exact hok w (hws_r.mem_iff.2 (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hw)))
        have hkept_perm : ((gp, gn, tg) :: kept ka (wa.p, wa.n, ta') (kept kb (wb.p, wb.n, tb') rest0)).Perm
            (child.map W.toPNT) := by
          cases ka <;> cases kb <;> simp only [child, kept, ite_true, ite_false, Bool.false_eq_true, List.map_cons, W.toPNT]
          · exact hrr.cons _
          · exact (hrr.cons _).cons _
          · exact (hrr.cons _).cons _
          · exact ((hrr.cons _).cons _).cons _
        have hrec_r : NatTRestricted top k (child.map W.toPNT) := natTRestricted_perm hkept_perm hrec
        have hrc_child : ∀ w ∈ child.map W.toPNT, RowColConst P N w.1 w.2.1 := by
          intro w hw
          have hm := hkept_perm.mem_iff.2 hw
          rcases List.mem_cons.1 hm with rfl | hm
          · exact hrc_g
          · cases ka <;> cases kb <;> simp only [kept, ite_true, ite_false, Bool.false_eq_true, List.mem_cons] at hm
            · exact hrc w (hp.mem_iff.2 (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hm)))
            · rcases hm with rfl | hmr
              · exact hrc_b
              · exact hrc w (hp.mem_iff.2 (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hmr)))
            · rcases hm with rfl | hmr
              · exact hrc_a
              · exact hrc w (hp.mem_iff.2 (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hmr)))
            · rcases hm with rfl | rfl | hmr
              · exact hrc_a
              · exact hrc_b
              · exact hrc w (hp.mem_iff.2 (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hmr)))
        exact hcb child hok_child hrc_child hrec_r
      have hdom_f : isDomW gp gn ws = false := isDomW_false_of_all (fun w hw => hdom w.toPNT (List.mem_map_of_mem hw))
      have hgp_b : Nat.beq gp 0 = false := by
        cases h : Nat.beq gp 0
        · rfl
        · exact absurd (Nat.eq_of_beq_eq_true h) hgp
      have hgn_b : Nat.beq gn top = false := by
        cases h : Nat.beq gn top
        · rfl
        · exact absurd (Nat.eq_of_beq_eq_true h) hgn
      have hda : ka = false → (if isOr then (u &&& wa.s &&& wb.n) = 0 else (u &&& wa.s &&& wb.p) = u &&& wa.s) := by
        intro hka; subst hka; rw [hwas]; exact drop_cond_ok hlt_lt hp hrec
      have hdb : kb = false → (if isOr then (u &&& wb.s &&& wa.n) = 0 else (u &&& wb.s &&& wa.p) = u &&& wb.s) := by
        intro hkb; subst hkb; rw [hwbs]
        have hrec_sw : NatTRestricted top k
            ((if isOr then (wb.p ||| wa.p) else (wb.p &&& wa.p),
              if isOr then (wb.n ||| wa.n) else (wb.n &&& wa.n),
              if !isOr && (Nat.beq wb.t 1 || Nat.beq wa.t 1) then 2 else 0) ::
             kept false (wb.p, wb.n, if isOr && Nat.beq wb.t 1 then 2 else wb.t)
               (kept ka (wa.p, wa.n, if isOr && Nat.beq wa.t 1 then 2 else wa.t) rest0)) := by
          have hcp : (if isOr then wb.p ||| wa.p else wb.p &&& wa.p) = gp := by cases isOr <;> simp [gp, Nat.and_comm, Nat.or_comm]
          have hcn : (if isOr then wb.n ||| wa.n else wb.n &&& wa.n) = gn := by cases isOr <;> simp [gn, Nat.and_comm, Nat.or_comm]
          have hct : (if !isOr && (Nat.beq wb.t 1 || Nat.beq wa.t 1) then 2 else 0) = tg := by rw [Bool.or_comm]
          rw [hcp, hcn, hct]
          dsimp only [kept, Bool.false_eq_true, ite_false]; exact hrec
        exact drop_cond_ok hlt_lt (hp.trans (List.Perm.swap _ _ _)) hrec_sw
      have hrl := natTRestricted_len k _ hrec
      have hpl := hp.length_eq
      have hwa_mk : W.mk wa.p wa.n wa.t wa.s = wa := by cases wa; rfl
      have hwb_mk : W.mk wb.p wb.n wb.t wb.s = wb := by cases wb; rfl
      by_cases hl2 : ws.length = k + 2
      · simp only [hl2, Nat.beq_refl]
        have hka : ka = false := by cases ka <;> cases kb <;> simp [kept] at hrl hpl hl2 hlen_eq ⊢ <;> omega
        have hkb : kb = false := by cases ka <;> cases kb <;> simp [kept] at hrl hpl hl2 hlen_eq ⊢ <;> omega
        refine scanFastW_of_pair hord (fun r hr => ?_)
        have hcb_ok := hcb_any r hr
        unfold fastPairW; simp only [nat_land_eq, nat_lor_eq, nat_xor_eq]
        cases isOr
        · apply match_or_true_left
          have h1' := h1.resolve_left (by decide)
          have hta2 : Nat.beq wa.t 2 = false := by cases h : Nat.beq wa.t 2; rfl; exact absurd (Nat.eq_of_beq_eq_true h) h1'.1
          have htb2 : Nat.beq wb.t 2 = false := by cases h : Nat.beq wb.t 2; rfl; exact absurd (Nat.eq_of_beq_eq_true h) h1'.2
          have hda' := hda hka; have hdb' := hdb hkb
          simp only [Bool.false_eq_true, ite_false] at hda' hdb'
          simp only [gp, gn, tg, hka, hkb, kept, Bool.false_eq_true, ite_false, Bool.not_false, Bool.true_and] at hcb_ok hdom_f hgp_b hgn_b
          simp only [hta2, htb2, hda', hdb', Nat.beq_refl, hgp_b, hgn_b, hdom_f, tg_match_eq, hcb_ok]
        · apply match_or_true_right
          have hda' := hda hka; have hdb' := hdb hkb
          simp only [ite_true] at hda' hdb'
          simp only [gp, gn, tg, hka, hkb, kept, ite_true, Bool.false_eq_true, ite_false, Bool.not_true, Bool.false_and] at hcb_ok hdom_f hgp_b hgn_b
          simp only [hda', hdb', Nat.beq_refl, hgp_b, hgn_b, hdom_f, hcb_ok]
      · have hl2b : Nat.beq ws.length (k + 2) = false := by cases h : Nat.beq ws.length (k + 2); rfl; exact absurd (Nat.eq_of_beq_eq_true h) hl2
        simp only [hl2b]
        by_cases hl1 : ws.length = k + 1
        · simp only [hl1, Nat.beq_refl]
          have hnotboth : ¬ (ka = true ∧ kb = true) := by
            intro ⟨hka, hkb⟩; subst hka; subst hkb; simp [kept] at hrl hpl hl1 hlen_eq; omega
          refine scanSlow1W_of_pair hord (fun r hr => ?_)
          have hcb_ok := hcb_any r hr
          unfold slow1PairW; simp only [nat_land_eq, nat_lor_eq, nat_xor_eq]
          cases isOr
          · apply match_or_true_left
            have h1' := h1.resolve_left (by decide)
            have hta2 : Nat.beq wa.t 2 = false := by cases h : Nat.beq wa.t 2; rfl; exact absurd (Nat.eq_of_beq_eq_true h) h1'.1
            have htb2 : Nat.beq wb.t 2 = false := by cases h : Nat.beq wb.t 2; rfl; exact absurd (Nat.eq_of_beq_eq_true h) h1'.2
            simp only [gp, gn, tg, ta', tb', Bool.false_eq_true, ite_false, Bool.not_false, Bool.true_and, Bool.false_and, hwa_mk, hwb_mk] at hcb_ok hdom_f hgp_b hgn_b
            cases ka <;> cases kb
            · have hda' := hda rfl; have hdb' := hdb rfl; simp only [Bool.false_eq_true, ite_false] at hda' hdb'
              simp only [kept, Bool.false_eq_true, ite_false] at hcb_ok
              simp only [hta2, htb2, hda', hdb', Nat.beq_refl, hgp_b, hgn_b, hdom_f, tg_match_eq]
              exact match_or_true_left hcb_ok
            · have hda' := hda rfl; simp only [Bool.false_eq_true, ite_false] at hda'
              have htb0 : Nat.beq wb.t 0 = true := by rcases h3 with h | h; contradiction; simp at h; simp [h]
              simp only [kept, ite_true, Bool.false_eq_true, ite_false] at hcb_ok
              simp only [hta2, htb2, hda', htb0, Nat.beq_refl, hgp_b, hgn_b, hdom_f, tg_match_eq, match_bool_const]
              exact match_or_true_right (match_or_true_right hcb_ok)
            · have hdb' := hdb rfl; simp only [Bool.false_eq_true, ite_false] at hdb'
              have hta0 : Nat.beq wa.t 0 = true := by rcases h2 with h | h; contradiction; simp at h; simp [h]
              simp only [kept, ite_true, Bool.false_eq_true, ite_false] at hcb_ok
              simp only [hta2, htb2, hdb', hta0, Nat.beq_refl, hgp_b, hgn_b, hdom_f, tg_match_eq, match_bool_const]
              exact match_or_true_right (match_or_true_left hcb_ok)
            · exact absurd ⟨rfl, rfl⟩ hnotboth
          · apply match_or_true_right
            simp only [gp, gn, tg, ta', tb', ite_true, Bool.not_true, Bool.false_and, Bool.true_and] at hcb_ok hdom_f hgp_b hgn_b
            cases ka <;> cases kb
            · have hda' := hda rfl; have hdb' := hdb rfl; simp only [ite_true] at hda' hdb'
              simp only [kept, Bool.false_eq_true, ite_false] at hcb_ok
              simp only [hda', hdb', Nat.beq_refl, hgp_b, hgn_b, hdom_f]
              exact match_or_true_left hcb_ok
            · have hda' := hda rfl; simp only [ite_true] at hda'
              have htb2 : Nat.beq wb.t 2 = false := by
                have h' : wb.t ≠ 2 := by rcases h3 with h | h; contradiction; simpa using h
                cases h : Nat.beq wb.t 2; rfl; exact absurd (Nat.eq_of_beq_eq_true h) h'
              simp only [kept, ite_true, Bool.false_eq_true, ite_false] at hcb_ok
              simp only [hda', htb2, Nat.beq_refl, hgp_b, hgn_b, hdom_f, ta_match_eq, match_bool_const]
              exact match_or_true_right (match_or_true_right hcb_ok)
            · have hdb' := hdb rfl; simp only [ite_true] at hdb'
              have hta2 : Nat.beq wa.t 2 = false := by
                have h' : wa.t ≠ 2 := by rcases h2 with h | h; contradiction; simpa using h
                cases h : Nat.beq wa.t 2; rfl; exact absurd (Nat.eq_of_beq_eq_true h) h'
              simp only [kept, ite_true, Bool.false_eq_true, ite_false] at hcb_ok
              simp only [hdb', hta2, Nat.beq_refl, hgp_b, hgn_b, hdom_f, ta_match_eq, match_bool_const]
              exact match_or_true_right (match_or_true_left hcb_ok)
            · exact absurd ⟨rfl, rfl⟩ hnotboth
        · have hl1b : Nat.beq ws.length (k + 1) = false := by cases h : Nat.beq ws.length (k + 1); rfl; exact absurd (Nat.eq_of_beq_eq_true h) hl1
          simp only [hl1b]
          refine scanSlow2W_of_pair hord (fun r hr => ?_)
          have hcb_ok := hcb_any r hr
          unfold slow2PairW; simp only [nat_land_eq, nat_lor_eq, nat_xor_eq]
          cases isOr
          · apply match_or_true_left
            have h1' := h1.resolve_left (by decide)
            have hta2 : Nat.beq wa.t 2 = false := by cases h : Nat.beq wa.t 2; rfl; exact absurd (Nat.eq_of_beq_eq_true h) h1'.1
            have htb2 : Nat.beq wb.t 2 = false := by cases h : Nat.beq wb.t 2; rfl; exact absurd (Nat.eq_of_beq_eq_true h) h1'.2
            simp only [gp, gn, tg, ta', tb', Bool.false_eq_true, ite_false, Bool.not_false, Bool.true_and, Bool.false_and, hwa_mk, hwb_mk] at hcb_ok hdom_f hgp_b hgn_b
            cases ka <;> cases kb
            · have hda' := hda rfl; have hdb' := hdb rfl; simp only [Bool.false_eq_true, ite_false] at hda' hdb'
              simp only [kept, Bool.false_eq_true, ite_false] at hcb_ok
              simp only [hta2, htb2, hda', hdb', Nat.beq_refl, hgp_b, hgn_b, hdom_f, tg_match_eq]
              exact match_or_true_left hcb_ok
            · have hda' := hda rfl; simp only [Bool.false_eq_true, ite_false] at hda'
              have htb0 : Nat.beq wb.t 0 = true := by rcases h3 with h | h; contradiction; simp at h; simp [h]
              simp only [kept, ite_true, Bool.false_eq_true, ite_false] at hcb_ok
              simp only [hta2, htb2, hda', htb0, Nat.beq_refl, hgp_b, hgn_b, hdom_f, tg_match_eq, match_bool_const]
              exact match_or_true_right (match_or_true_right (match_or_true_left hcb_ok))
            · have hdb' := hdb rfl; simp only [Bool.false_eq_true, ite_false] at hdb'
              have hta0 : Nat.beq wa.t 0 = true := by rcases h2 with h | h; contradiction; simp at h; simp [h]
              simp only [kept, ite_true, Bool.false_eq_true, ite_false] at hcb_ok
              simp only [hta2, htb2, hdb', hta0, Nat.beq_refl, hgp_b, hgn_b, hdom_f, tg_match_eq, match_bool_const]
              exact match_or_true_right (match_or_true_left hcb_ok)
            · have hta0 : Nat.beq wa.t 0 = true := by rcases h2 with h | h; contradiction; simp at h; simp [h]
              have htb0 : Nat.beq wb.t 0 = true := by rcases h3 with h | h; contradiction; simp at h; simp [h]
              simp only [kept, ite_true] at hcb_ok
              simp only [hta2, htb2, hta0, htb0, hgp_b, hgn_b, hdom_f, tg_match_eq, match_bool_const]
              exact match_or_true_right (match_or_true_right (match_or_true_right hcb_ok))
          · apply match_or_true_right
            simp only [gp, gn, tg, ta', tb', ite_true, Bool.not_true, Bool.false_and, Bool.true_and] at hcb_ok hdom_f hgp_b hgn_b
            cases ka <;> cases kb
            · have hda' := hda rfl; have hdb' := hdb rfl; simp only [ite_true] at hda' hdb'
              simp only [kept, Bool.false_eq_true, ite_false] at hcb_ok
              simp only [hda', hdb', Nat.beq_refl, hgp_b, hgn_b, hdom_f]
              exact match_or_true_left hcb_ok
            · have hda' := hda rfl; simp only [ite_true] at hda'
              have htb2 : Nat.beq wb.t 2 = false := by
                have h' : wb.t ≠ 2 := by rcases h3 with h | h; contradiction; simpa using h
                cases h : Nat.beq wb.t 2; rfl; exact absurd (Nat.eq_of_beq_eq_true h) h'
              simp only [kept, ite_true, Bool.false_eq_true, ite_false] at hcb_ok
              simp only [hda', htb2, Nat.beq_refl, hgp_b, hgn_b, hdom_f, ta_match_eq, match_bool_const]
              exact match_or_true_right (match_or_true_right (match_or_true_left hcb_ok))
            · have hdb' := hdb rfl; simp only [ite_true] at hdb'
              have hta2 : Nat.beq wa.t 2 = false := by
                have h' : wa.t ≠ 2 := by rcases h2 with h | h; contradiction; simpa using h
                cases h : Nat.beq wa.t 2; rfl; exact absurd (Nat.eq_of_beq_eq_true h) h'
              simp only [kept, ite_true, Bool.false_eq_true, ite_false] at hcb_ok
              simp only [hdb', hta2, Nat.beq_refl, hgp_b, hgn_b, hdom_f, ta_match_eq, match_bool_const]
              exact match_or_true_right (match_or_true_left hcb_ok)
            · have hta2 : Nat.beq wa.t 2 = false := by
                have h' : wa.t ≠ 2 := by rcases h2 with h | h; contradiction; simpa using h
                cases h : Nat.beq wa.t 2; rfl; exact absurd (Nat.eq_of_beq_eq_true h) h'
              have htb2 : Nat.beq wb.t 2 = false := by
                have h' : wb.t ≠ 2 := by rcases h3 with h | h; contradiction; simpa using h
                cases h : Nat.beq wb.t 2; rfl; exact absurd (Nat.eq_of_beq_eq_true h) h'
              simp only [kept, ite_true, Bool.false_eq_true, ite_false] at hcb_ok
              simp only [hta2, htb2, hgp_b, hgn_b, hdom_f, ta_match_eq, match_bool_const]
              exact match_or_true_right (match_or_true_right (match_or_true_right hcb_ok))
lemma searchCertW_complete {P N m1 m2 m4 m8 rowStart rowFull : Nat}
    {certHit : Nat → List W → Bool}
    (hN : 0 < N) (hrf : rowFull = (1 <<< N) - 1) (hrs : RowStartOk P N rowStart)
    (hm1 : MaskLoOk P N 1 m1) (hm2 : MaskLoOk P N 2 m2)
    (hm4 : MaskLoOk P N 4 m4) (hm8 : MaskLoOk P N 8 m8)
    (cap : Nat)
    (hcert : ∀ s ≤ cap, ∀ zs, (∀ w ∈ zs.map W.toPNT, RowColConst P N w.1 w.2.1) →
      NatTRestricted (2 ^ (P * N) - 1) s (zs.map W.toPNT) → certHit s zs = false) :
    let c : Cfg := ⟨2 ^ (P * N) - 1, N, Nat.mul 2 N, Nat.mul 4 N, Nat.mul 8 N, m1, m2, m4, m8, rowStart, rowFull, certHit⟩
    ∀ s ≤ cap, ∀ ws, WOk (2 ^ (P * N) - 1) ws →
      (∀ w ∈ ws.map W.toPNT, RowColConst P N w.1 w.2.1) →
      NatTRestricted (2 ^ (P * N) - 1) s (ws.map W.toPNT) →
      searchCertW c s ws = true := by
  intro c s
  induction s with
  | zero =>
    rintro _ ws _ _ ⟨t, hmap⟩
    cases ws with
    | nil => simp at hmap
    | cons w rest =>
      cases rest with
      | cons _ _ => simp at hmap
      | nil =>
        simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true, W.toPNT, Prod.mk.injEq] at hmap
        simp [searchCertW, c, hmap.1, hmap.2.1]
  | succ s ih =>
    intro hs ws hok hrc h
    have ⟨hlen, hc1, hcr, hscan⟩ := step_body_completeW hN hrf hrs hm1 hm2 hm4 hm8 hok hrc h
      (fun zs hokz hrcz hz => ih (by omega) zs hokz hrcz hz)
    have hcert_f := hcert (s + 1) hs ws hrc h
    have hble : Nat.ble (s + 3) ws.length = false := by
      cases hb : Nat.ble (s + 3) ws.length; rfl
      have := Nat.le_of_ble_eq_true hb; omega
    cases ws with
    | nil =>
      obtain ⟨_, _, _, _, _, _, _, _, _, _, hp, _⟩ := h
      have := hp.length_eq; simp at this
    | cons w1 t1 =>
      cases t1 with
      | nil =>
        obtain ⟨_, _, _, _, _, _, _, _, _, _, hp, _⟩ := h
        have := hp.length_eq; simp at this
      | cons w2 t2 =>
        dsimp only [searchCertW]
        rw [covPass_eq _ _ 0 0 0 hok]; dsimp only
        simp only [Nat.add_zero, nat_add_eq, nat_xor_eq, c]
        rw [hble]; dsimp only
        rw [hc1] at hcr hscan ⊢
        rw [Nat.beq_refl]; dsimp only
        have hkilled : (match Nat.beq (w1 :: w2 :: t2).length (s + 2) with
            | true => hasCrossW c ((2 ^ (P * N) - 1) ^^^ (buildSeps (2 ^ (P * N) - 1) ((w1 :: w2 :: t2).map W.toPNT) 0 0).2.2)
                (buildSeps (2 ^ (P * N) - 1) ((w1 :: w2 :: t2).map W.toPNT) 0 0).2.2 (w1 :: w2 :: t2) 0
            | false => false) = false := by
          cases hb : Nat.beq (w1 :: w2 :: t2).length (s + 2)
          · rfl
          · rw [hasCrossW_eq c rfl rfl rfl]
            exact hcr (Nat.eq_of_beq_eq_true hb)
        rw [hkilled]; dsimp only
        rw [hcert_f]; exact hscan
lemma stepExpand_complete {P N m1 m2 m4 m8 rowStart rowFull : Nat}
    {certHit : Nat → List W → Bool}
    (hN : 0 < N) (hrf : rowFull = (1 <<< N) - 1) (hrs : RowStartOk P N rowStart)
    (hm1 : MaskLoOk P N 1 m1) (hm2 : MaskLoOk P N 2 m2)
    (hm4 : MaskLoOk P N 4 m4) (hm8 : MaskLoOk P N 8 m8)
    {k : Nat} {ws : List W}
    (hcert : ∀ s < k, ∀ zs, (∀ w ∈ zs.map W.toPNT, RowColConst P N w.1 w.2.1) →
      NatTRestricted (2 ^ (P * N) - 1) s (zs.map W.toPNT) → certHit s zs = false)
    (hok : WOk (2 ^ (P * N) - 1) ws)
    (hrc : ∀ w ∈ ws.map W.toPNT, RowColConst P N w.1 w.2.1)
    (h : NatTRestricted (2 ^ (P * N) - 1) k (ws.map W.toPNT)) :
    stepExpand (2 ^ (P * N) - 1) N m1 m2 m4 m8 rowStart rowFull certHit k ws = true := by
  cases k with
  | zero =>
    obtain ⟨t, hmap⟩ := h
    cases ws with
    | nil => simp at hmap
    | cons w rest =>
      cases rest with
      | cons _ _ => simp at hmap
      | nil =>
        simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true, W.toPNT, Prod.mk.injEq] at hmap
        simp [stepExpand, hmap.1, hmap.2.1]
  | succ k =>
    have hcb := searchCertW_complete hN hrf hrs hm1 hm2 hm4 hm8 k
      (fun s hs => hcert s (by omega))
    have ⟨hlen, hc1, hcr, hscan⟩ := step_body_completeW hN hrf hrs hm1 hm2 hm4 hm8 hok hrc h
      (fun zs hokz hrcz hz => hcb k (Nat.le_refl k) zs hokz hrcz hz)
    have hble : Nat.ble (k + 3) ws.length = false := by
      cases hb : Nat.ble (k + 3) ws.length; rfl
      have := Nat.le_of_ble_eq_true hb; omega
    cases ws with
    | nil => obtain ⟨_, _, _, _, _, _, _, _, _, _, hp, _⟩ := h; have := hp.length_eq; simp at this
    | cons w1 t1 =>
      cases t1 with
      | nil => obtain ⟨_, _, _, _, _, _, _, _, _, _, hp, _⟩ := h; have := hp.length_eq; simp at this
      | cons w2 t2 =>
        dsimp only [stepExpand]
        rw [covPass_eq _ _ 0 0 0 hok]; dsimp only
        simp only [Nat.add_zero, nat_add_eq, nat_xor_eq]
        rw [hble]; dsimp only
        rw [hc1] at hcr hscan ⊢
        rw [Nat.beq_refl]; dsimp only
        set c : Cfg := ⟨2 ^ (P * N) - 1, N, Nat.mul 2 N, Nat.mul 4 N, Nat.mul 8 N, m1, m2, m4, m8, rowStart, rowFull, certHit⟩
        have hkilled : (match Nat.beq (w1 :: w2 :: t2).length (k + 2) with
            | true => hasCrossW c ((2 ^ (P * N) - 1) ^^^ (buildSeps (2 ^ (P * N) - 1) ((w1 :: w2 :: t2).map W.toPNT) 0 0).2.2)
                (buildSeps (2 ^ (P * N) - 1) ((w1 :: w2 :: t2).map W.toPNT) 0 0).2.2 (w1 :: w2 :: t2) 0
            | false => false) = false := by
          cases hb : Nat.beq (w1 :: w2 :: t2).length (k + 2)
          · rfl
          · rw [hasCrossW_eq c rfl rfl rfl]
            exact hcr (Nat.eq_of_beq_eq_true hb)
        rw [hkilled]; exact hscan
def span (f : Nat → Bool) : Nat → Nat → Bool
  | 0, _ => true
  | n + 1, i => match f i with | true => span f n (Nat.add i 1) | false => false
lemma span_ok {f : Nat → Bool} {n o : Nat} (h : span f n o = true) :
    ∀ i, o ≤ i → i < o + n → f i = true := by
  induction n generalizing o with
  | zero => intro i hi hj; omega
  | succ n ih =>
    dsimp only [span] at h
    rw [nat_add_eq] at h
    cases hf : f o <;> simp only [hf] at h
    · contradiction
    · intro i hi hj
      rcases Nat.eq_or_lt_of_le hi with rfl | hlt
      · exact hf
      · exact ih h i (by omega) (by omega)
lemma sr {f : Nat → Bool} {n o hi : Nat} (hhi : o + n = hi) (h : span f n o = true) :
    ∀ i, o ≤ i → i < hi → f i = true := by
  subst hhi; exact span_ok h
lemma rj {f : Nat → Bool} {a b c : Nat}
    (h1 : ∀ i, a ≤ i → i < b → f i = true)
    (h2 : ∀ i, b ≤ i → i < c → f i = true) :
    ∀ i, a ≤ i → i < c → f i = true := fun i ha hc =>
  if hlt : i < b then h1 i ha hlt else h2 i (Nat.le_of_not_lt hlt) hc
def wireHash (salt p n t : Nat) : Nat :=
  let h := Nat.mod (Nat.add (Nat.add (Nat.add (Nat.mul (Nat.mod p 1048573) (Nat.add 65537 salt)) (Nat.mul (Nat.mod n 1048573) 131)) (Nat.mul t 997)) 317) 1048573
  Nat.mod (Nat.mul (Nat.mod (Nat.mul h h) 1048573) h) 1048573
def stateHash (salt : Nat) : List W → Nat
  | [] => 0
  | w :: rest => Nat.add (wireHash salt w.p w.n w.t) (stateHash salt rest)
def htProbe (salt buckets mult T dw dmask cw cmask : Nat) (htd hta : Nat → Nat)
    (zs : List W) : Nat :=
  let h := Nat.mod (stateHash salt zs) 1048573
  let b := Nat.mod h buckets
  let d := Nat.land (Nat.shiftRight (htd (Nat.shiftRight b 7)) (Nat.mul (Nat.land b 127) dw)) dmask
  let s := Nat.mod (Nat.add (Nat.mod (Nat.mul h mult) 1048573) d) T
  Nat.land (Nat.shiftRight (hta (Nat.shiftRight s 7)) (Nat.mul (Nat.land s 127) cw)) cmask
def stProbe (sb : Nat) (st : Nat → Nat) (decL : Nat → Nat → List W)
    (idx : Nat) : List W :=
  let raw := Nat.shiftRight (st (Nat.shiftRight idx 5)) (Nat.mul (Nat.land idx 31) sb)
  decL (Nat.land raw 15) (Nat.shiftRight raw 4)
def checkMaskLo (P N k m : Nat) : Bool :=
  (List.range P).all fun i => (List.range N).all fun j => !m.testBit (i * N + j) || decide (j + k < N)
lemma checkMaskLo_ok {P N k m : Nat} (h : checkMaskLo P N k m = true) : MaskLoOk P N k m := by
  intro i hi j hj htb
  simp only [checkMaskLo, List.all_eq_true, List.mem_range, Bool.or_eq_true, Bool.not_eq_true', decide_eq_true_eq] at h
  rcases h i hi j hj with hf | hlt
  · rw [htb] at hf; contradiction
  · exact hlt
lemma dag_impossible {P N m1 m2 m4 m8 rowStart rowFull : Nat}
    {cnt : Nat → Nat} {decSt : Nat → Nat → List W}
    {certHit : Nat → List W → Bool}
    (hN : 0 < N) (hrf : rowFull = (1 <<< N) - 1) (hrs : RowStartOk P N rowStart)
    (hm1 : MaskLoOk P N 1 m1) (hm2 : MaskLoOk P N 2 m2)
    (hm4 : MaskLoOk P N 4 m4) (hm8 : MaskLoOk P N 8 m8)
    (hdec_ok : ∀ s idx, WOk (2 ^ (P * N) - 1) (decSt s idx))
    (hcert_sound : ∀ s zs, (∀ w ∈ zs.map W.toPNT, RowColConst P N w.1 w.2.1) →
      NatTRestricted (2 ^ (P * N) - 1) s (zs.map W.toPNT) → certHit s zs = true →
      ∃ idx < cnt s, (∀ w ∈ (decSt s idx).map W.toPNT, RowColConst P N w.1 w.2.1) ∧
        NatTRestricted (2 ^ (P * N) - 1) s ((decSt s idx).map W.toPNT))
    (cap : Nat)
    (hcheck : ∀ s ≤ cap, ∀ idx < cnt s,
      stepExpand (2 ^ (P * N) - 1) N m1 m2 m4 m8 rowStart rowFull certHit s (decSt s idx) = false) :
    ∀ s ≤ cap, ∀ idx < cnt s,
      ¬ ((∀ w ∈ (decSt s idx).map W.toPNT, RowColConst P N w.1 w.2.1) ∧
         NatTRestricted (2 ^ (P * N) - 1) s ((decSt s idx).map W.toPNT)) := by
  intro s
  induction s using Nat.strong_induction_on with
  | ind s ih =>
    intro hs idx hidx ⟨hrc, hnat⟩
    have hcf : ∀ q < s, ∀ zs, (∀ w ∈ zs.map W.toPNT, RowColConst P N w.1 w.2.1) →
        NatTRestricted (2 ^ (P * N) - 1) q (zs.map W.toPNT) → certHit q zs = false := by
      intro q hq zs hrcz hz
      cases hc : certHit q zs
      · rfl
      · obtain ⟨j, hj, hrcj, hnatj⟩ := hcert_sound q zs hrcz hz hc
        exact absurd ⟨hrcj, hnatj⟩ (ih q hq (by omega) j hj)
    have ht := stepExpand_complete hN hrf hrs hm1 hm2 hm4 hm8 hcf (hdec_ok s idx) hrc hnat
    rw [hcheck s hs idx hidx] at ht; contradiction
lemma root_impossible {P N m1 m2 m4 m8 rowStart rowFull : Nat}
    {cnt : Nat → Nat} {decSt : Nat → Nat → List W}
    {certHit : Nat → List W → Bool}
    (hN : 0 < N) (hrf : rowFull = (1 <<< N) - 1) (hrs : RowStartOk P N rowStart)
    (hm1 : MaskLoOk P N 1 m1) (hm2 : MaskLoOk P N 2 m2)
    (hm4 : MaskLoOk P N 4 m4) (hm8 : MaskLoOk P N 8 m8)
    (hdec_ok : ∀ s idx, WOk (2 ^ (P * N) - 1) (decSt s idx))
    (hcert_sound : ∀ s zs, (∀ w ∈ zs.map W.toPNT, RowColConst P N w.1 w.2.1) →
      NatTRestricted (2 ^ (P * N) - 1) s (zs.map W.toPNT) → certHit s zs = true →
      ∃ idx < cnt s, (∀ w ∈ (decSt s idx).map W.toPNT, RowColConst P N w.1 w.2.1) ∧
        NatTRestricted (2 ^ (P * N) - 1) s ((decSt s idx).map W.toPNT))
    (cap : Nat)
    (hcheck : ∀ s ≤ cap, ∀ idx < cnt s,
      stepExpand (2 ^ (P * N) - 1) N m1 m2 m4 m8 rowStart rowFull certHit s (decSt s idx) = false)
    {k : Nat} (hk : k ≤ cap) {ws : List W}
    (hroot : searchCert (2 ^ (P * N) - 1) N m1 m2 m4 m8 rowStart rowFull certHit k ws = false)
    (hok : WOk (2 ^ (P * N) - 1) ws)
    (hrc : ∀ w ∈ ws.map W.toPNT, RowColConst P N w.1 w.2.1)
    (hnat : NatTRestricted (2 ^ (P * N) - 1) k (ws.map W.toPNT)) : False := by
  have hdag := dag_impossible hN hrf hrs hm1 hm2 hm4 hm8 hdec_ok hcert_sound cap hcheck
  have hcf : ∀ s ≤ cap, ∀ zs, (∀ w ∈ zs.map W.toPNT, RowColConst P N w.1 w.2.1) →
      NatTRestricted (2 ^ (P * N) - 1) s (zs.map W.toPNT) → certHit s zs = false := by
    intro s hs zs hrcz hz
    cases hc : certHit s zs
    · rfl
    · obtain ⟨j, hj, hrcj, hnatj⟩ := hcert_sound s zs hrcz hz hc
      exact absurd ⟨hrcj, hnatj⟩ (hdag s hs j hj)
  have ht := searchCertW_complete hN hrf hrs hm1 hm2 hm4 hm8 cap hcf k hk ws hok hrc hnat
  unfold searchCert at hroot
  rw [hroot] at ht; contradiction
lemma instant_kill {pos neg pos' neg' : List Nat} {W W' : List F9} {k k_c : Nat}
    (v : Fin 9) (π : Fin 9 → Fin 9) (e m : Nat)
    (hpos_ne : pos ≠ []) (hneg_ne : neg ≠ [])
    (hWmono : ∀ w ∈ W, IsMono w)
    (he : e ∈ pos) (hm : m ∈ neg)
    (huniq : ∀ w ∈ W, w (maskToV e) = true → w (maskToV m) = false → w = varF v)
    (hk : k - 1 ≤ k_c)
    (hpos' : ∀ e' ∈ pos', pullMask π e' ∈ pos ∧ (pullMask π e').testBit v.1 = false)
    (hneg' : ∀ m' ∈ neg', (pullMask π m').testBit v.1 = false ∧
      ∃ m0 ∈ neg, (pullMask π m' &&& m0) = pullMask π m')
    (hpos'_ne : pos' ≠ []) (hneg'_ne : neg' ≠ [])
    (hW' : ∀ w ∈ W, (∃ w' ∈ W', dominates pos' neg' (permF π (projV v w)) w') ∨
      dominates pos' neg' (permF π (projV v w)) (fun _ => false))
    (hchild : ¬ HasMono pos' neg' W' k_c) :
    ¬ HasMono pos neg W k := by
  intro h
  obtain ⟨k1, hk1, hm1⟩ := hasMono_to_monoLive hpos_ne hneg_ne k W h
  obtain ⟨k2, hk2, U, hUW, _, hSU⟩ := monoLive_to_sMonoLive k1 W hm1
  obtain ⟨w, hwU, hwe, hwm⟩ := sMonoLive_covers k2 U hSU e he m hm
  have hwv : w = varF v := huniq w (hUW w hwU) hwe hwm
  subst hwv
  have hUmono : ∀ u ∈ U, IsMono u := fun u hu => hWmono u (hUW u hu)
  let pos_v := pos'.map (pullMask π)
  let neg_v := neg'.map (pullMask π)
  have hsv : SubValid pos neg v pos_v neg_v := by
    refine ⟨by simp [pos_v, hpos'_ne], by simp [neg_v, hneg'_ne], ?_, ?_⟩
    · intro x hx; rw [List.mem_map] at hx; obtain ⟨e', he', rfl⟩ := hx; exact hpos' e' he'
    · intro x hx; rw [List.mem_map] at hx; obtain ⟨m', hm', rfl⟩ := hx; exact hneg' m' hm'
  have hzv : projV v (varF v) = fun _ => false := by funext x; simp [projV, varF]
  obtain ⟨_, hhm⟩ := one_zero_wire_save_one hsv k2 U hUmono hSU (varF v) hwU hzv
  have hhm_W : HasMono pos_v neg_v (W.map (projV v)) k_c :=
    hasMono_mono_k (by omega) (hasMono_mono_W (fun u hu => by
      rw [List.mem_map] at hu ⊢; obtain ⟨w0, hw0, rfl⟩ := hu; exact ⟨w0, hUW w0 hw0, rfl⟩) hhm)
  obtain ⟨f, hf, hag⟩ := hhm_W
  have hfp : MonoReach k_c ((W.map (projV v)).map (permF π)) (permF π f) := monoReach_permF π hf
  have hag' : agrees pos' neg' (permF π f) := by
    refine ⟨fun e' he' => ?_, fun m' hm' => ?_⟩
    · show f (fun i => maskToV e' (π i)) = true
      rw [← maskToV_pullMask]; exact hag.1 _ (List.mem_map_of_mem he')
    · show f (fun i => maskToV m' (π i)) = false
      rw [← maskToV_pullMask]; exact hag.2 _ (List.mem_map_of_mem hm')
  have hHas2 : HasMono pos' neg' ((fun _ => false) :: W') k_c := by
    apply hasMono_dom _ ⟨permF π f, hfp, hag'⟩
    intro u hu; rw [List.mem_map] at hu; obtain ⟨u1, hu1, rfl⟩ := hu
    rw [List.mem_map] at hu1; obtain ⟨w0, hw0, rfl⟩ := hu1
    rcases hW' w0 hw0 with ⟨w', hw', hd⟩ | hd
    · exact ⟨w', List.mem_cons_of_mem _ hw', hd⟩
    · exact ⟨_, List.mem_cons_self, hd⟩
  exact hchild (hasMono_drop_false hHas2)
lemma no_projV_of_child {pos' neg' : List Nat} {W W' U : List F9} {q : Nat}
    (v : Fin 9) (π : Fin 9 → Fin 9)
    (hUW : ∀ u ∈ U, u ∈ W)
    (hW' : ∀ w ∈ W, (∃ w' ∈ W', dominates pos' neg' (permF π (projV v w)) w') ∨
      dominates pos' neg' (permF π (projV v w)) (fun _ => false))
    (hchild : ¬ HasMono pos' neg' W' q) :
    ¬ HasMono (pos'.map (pullMask π)) (neg'.map (pullMask π)) (U.map (projV v)) q := by
  intro hhm
  have hhm_W : HasMono (pos'.map (pullMask π)) (neg'.map (pullMask π)) (W.map (projV v)) q :=
    hasMono_mono_W (fun u hu => by
      rw [List.mem_map] at hu ⊢; obtain ⟨w0, hw0, rfl⟩ := hu; exact ⟨w0, hUW w0 hw0, rfl⟩) hhm
  obtain ⟨f, hf, hag⟩ := hhm_W
  have hfp : MonoReach q ((W.map (projV v)).map (permF π)) (permF π f) := monoReach_permF π hf
  have hag' : agrees pos' neg' (permF π f) := by
    refine ⟨fun e' he' => ?_, fun m' hm' => ?_⟩
    · show f (fun i => maskToV e' (π i)) = true
      rw [← maskToV_pullMask]; exact hag.1 _ (List.mem_map_of_mem he')
    · show f (fun i => maskToV m' (π i)) = false
      rw [← maskToV_pullMask]; exact hag.2 _ (List.mem_map_of_mem hm')
  have hHas2 : HasMono pos' neg' ((fun _ => false) :: W') q := by
    apply hasMono_dom _ ⟨permF π f, hfp, hag'⟩
    intro u hu; rw [List.mem_map] at hu; obtain ⟨u1, hu1, rfl⟩ := hu
    rw [List.mem_map] at hu1; obtain ⟨w0, hw0, rfl⟩ := hu1
    rcases hW' w0 hw0 with ⟨w', hw', hd⟩ | hd
    · exact ⟨w', List.mem_cons_of_mem _ hw', hd⟩
    · exact ⟨_, List.mem_cons_self, hd⟩
  exact hchild (hasMono_drop_false hHas2)
lemma nodup_perm_of_subset {α : Type} {U B : List α}
    (hUnd : U.Nodup) (hBnd : B.Nodup)
    (h1 : ∀ x ∈ U, x ∈ B) (h2 : ∀ x ∈ B, x ∈ U) : U.Perm B := by
  classical
  exact (List.perm_ext_iff_of_nodup hUnd hBnd).2 fun x => ⟨h1 x, h2 x⟩
lemma nodup_perm_or_cons {α : Type} {U B : List α} {extra : α}
    (hUnd : U.Nodup) (hBnd : B.Nodup) (hex : extra ∉ B)
    (h1 : ∀ x ∈ U, x ∈ B ∨ x = extra) (h2 : ∀ x ∈ B, x ∈ U) :
    U.Perm B ∨ U.Perm (B ++ [extra]) := by
  classical
  by_cases he : extra ∈ U
  · right
    have hBnd2 : (B ++ [extra]).Nodup := by
      rw [List.nodup_append]; exact ⟨hBnd, List.nodup_singleton extra, fun x hx y hy hxy => by
        rcases List.mem_singleton.1 hy with rfl; subst hxy; exact hex hx⟩
    exact (List.perm_ext_iff_of_nodup hUnd hBnd2).2 fun x =>
      ⟨fun hx => by rcases h1 x hx with hb | rfl; exact List.mem_append_left _ hb; exact List.mem_append_right _ List.mem_cons_self,
       fun hx => by rcases List.mem_append.1 hx with hb | h; exact h2 x hb; rcases List.mem_singleton.1 h with rfl; exact he⟩
  · left
    exact nodup_perm_of_subset hUnd hBnd (fun x hx => (h1 x hx).resolve_right (fun h => he (h ▸ hx))) h2
lemma varF_ne {i j : Fin 9} (h : i ≠ j) : varF i ≠ varF j := fun heq => by
  have := congrFun heq (fun k => decide (k = i))
  simp [varF, h.symm] at this
lemma w9F_ne_varF (i : Fin 9) : w9F ≠ varF i := fun heq => by
  have h1 := congrFun heq (fun k => decide (k ≠ i))
  simp only [w9F, varF, ne_eq, not_true_eq_false, decide_false] at h1
  by_cases h0 : (0 : Fin 9) = i
  · subst h0; simp at h1
  · simp [h0] at h1
lemma root_input_map (m : Nat) :
    ([varF ⟨0, by decide⟩, varF ⟨1, by decide⟩, varF ⟨2, by decide⟩,
      varF ⟨3, by decide⟩, varF ⟨4, by decide⟩, varF ⟨5, by decide⟩,
      varF ⟨6, by decide⟩, varF ⟨7, by decide⟩, varF ⟨8, by decide⟩, w9F].map (· (maskToV m))) =
    ((List.ofFn fun (x5 : Fin 9) => m.testBit ↑x5) ++ [m.testBit 0 || m.testBit 1]) := by
  simp [List.ofFn_succ, maskToV, varF, w9F]
def checkSubPos (pos pos' : List Nat) (v : Fin 9) (π : Fin 9 → Fin 9) : Bool :=
  pos'.all fun e' => (pos.any fun e => Nat.beq e (pullMask π e')) && !(pullMask π e').testBit v.1
lemma checkSubPos_ok {pos pos' : List Nat} {v : Fin 9} {π : Fin 9 → Fin 9}
    (h : checkSubPos pos pos' v π = true) :
    ∀ e' ∈ pos', pullMask π e' ∈ pos ∧ (pullMask π e').testBit v.1 = false := by
  intro e' he'
  simp only [checkSubPos, List.all_eq_true, Bool.and_eq_true, List.any_eq_true, Nat.beq_eq,
    Bool.not_eq_true'] at h
  obtain ⟨⟨e, he, heq⟩, hbit⟩ := h e' he'
  exact ⟨heq ▸ he, hbit⟩
def checkSubNeg (neg neg' : List Nat) (v : Fin 9) (π : Fin 9 → Fin 9) : Bool :=
  neg'.all fun m' => !(pullMask π m').testBit v.1 &&
    (neg.any fun m0 => Nat.beq (pullMask π m' &&& m0) (pullMask π m'))
lemma checkSubNeg_ok {neg neg' : List Nat} {v : Fin 9} {π : Fin 9 → Fin 9}
    (h : checkSubNeg neg neg' v π = true) :
    ∀ m' ∈ neg', (pullMask π m').testBit v.1 = false ∧ ∃ m0 ∈ neg, (pullMask π m' &&& m0) = pullMask π m' := by
  intro m' hm'
  simp only [checkSubNeg, List.all_eq_true, Bool.and_eq_true, List.any_eq_true, Nat.beq_eq,
    Bool.not_eq_true'] at h
  exact h m' hm'
lemma subValid_of_checks {pos neg pos' neg' : List Nat} {v : Fin 9} {π : Fin 9 → Fin 9}
    (hpne : pos' ≠ []) (hnne : neg' ≠ [])
    (hp : checkSubPos pos pos' v π = true) (hn : checkSubNeg neg neg' v π = true) :
    SubValid pos neg v (pos'.map (pullMask π)) (neg'.map (pullMask π)) := by
  refine ⟨by simp [hpne], by simp [hnne], ?_, ?_⟩
  · intro x hx; rw [List.mem_map] at hx; obtain ⟨e', he', rfl⟩ := hx; exact checkSubPos_ok hp e' he'
  · intro x hx; rw [List.mem_map] at hx; obtain ⟨m', hm', rfl⟩ := hx; exact checkSubNeg_ok hn m' hm'
def checkDom (pos neg : List Nat) (g w : F9) : Bool :=
  (pos.all fun e => !g (maskToV e) || w (maskToV e)) &&
  (neg.all fun m => !w (maskToV m) || g (maskToV m))
lemma checkDom_ok {pos neg : List Nat} {g w : F9} (h : checkDom pos neg g w = true) :
    dominates pos neg g w := by
  simp only [checkDom, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at h
  refine ⟨fun m hm hg => ?_, fun m hm hw => ?_⟩
  · rcases h.1 m hm with hf | ht; rw [hg] at hf; contradiction; exact ht
  · rcases h.2 m hm with hf | ht; rw [hw] at hf; contradiction; exact ht
lemma sMonoLive_len {pos neg : List Nat} :
    ∀ k W, SMonoLive pos neg k W → W.length ≤ k + 1 := by
  intro k
  induction k with
  | zero => rintro W ⟨f, rfl, _⟩; simp
  | succ k ih =>
    intro W ⟨a, b, rest, isOr, ka, kb, hp, _, _, _, hrec⟩
    have hl := hp.length_eq
    have hr := ih _ hrec
    cases ka <;> cases kb <;> simp only [kept, ite_true, ite_false, Bool.false_eq_true, List.length_cons] at hr hl ⊢ <;> omega
lemma direct_impossible {P N m1 m2 m4 m8 rowStart rowFull k : Nat}
    {ws : List W}
    (hN : 0 < N) (hrf : rowFull = (1 <<< N) - 1) (hrs : RowStartOk P N rowStart)
    (hm1 : MaskLoOk P N 1 m1) (hm2 : MaskLoOk P N 2 m2)
    (hm4 : MaskLoOk P N 4 m4) (hm8 : MaskLoOk P N 8 m8)
    (hdir : searchCert (2 ^ (P * N) - 1) N m1 m2 m4 m8 rowStart rowFull (fun _ _ => false) k ws = false)
    (hok : WOk (2 ^ (P * N) - 1) ws)
    (hrc : ∀ w ∈ ws.map W.toPNT, RowColConst P N w.1 w.2.1)
    (hnat : NatTRestricted (2 ^ (P * N) - 1) k (ws.map W.toPNT)) : False := by
  have ht := searchCertW_complete hN hrf hrs hm1 hm2 hm4 hm8 k
    (fun _ _ _ _ _ => rfl) k (Nat.le_refl k) ws hok hrc hnat
  unfold searchCert at hdir
  rw [hdir] at ht; contradiction
def mapInv (fixP : Nat) (swP : List (Nat × Nat)) (fixN : Nat) (swN : List (Nat × Nat)) :
    List W → List W
  | [] => []
  | w :: rest => ⟨applyInv fixP swP w.p, applyInv fixN swN w.n, w.t, 0⟩ :: mapInv fixP swP fixN swN rest
lemma mapInv_toPNT (fixP : Nat) (swP : List (Nat × Nat)) (fixN : Nat) (swN : List (Nat × Nat)) :
    ∀ zs, (mapInv fixP swP fixN swN zs).map W.toPNT =
      (zs.map W.toPNT).map fun (p, n, t) => (applyInv fixP swP p, applyInv fixN swN n, t)
  | [] => rfl
  | w :: rest => by simp [mapInv, W.toPNT, mapInv_toPNT fixP swP fixN swN rest]
lemma inv_list_sound {P N fixP fixN : Nat} {swapsP swapsN : List (Nat × Nat)}
    (hvP : invValid (2 ^ (P * N) - 1) fixP swapsP = true)
    (hvN : invValid (2 ^ (P * N) - 1) fixN swapsN = true)
    (hrP : rowInvOk P N fixP swapsP = true)
    (hcN : colInvOk P N fixN swapsN = true)
    {k : Nat} {zs : List W}
    (hrc : ∀ w ∈ zs.map W.toPNT, RowColConst P N w.1 w.2.1)
    (hnat : NatTRestricted (2 ^ (P * N) - 1) k (zs.map W.toPNT)) :
    (∀ w ∈ (mapInv fixP swapsP fixN swapsN zs).map W.toPNT, RowColConst P N w.1 w.2.1) ∧
    NatTRestricted (2 ^ (P * N) - 1) k ((mapInv fixP swapsP fixN swapsN zs).map W.toPNT) := by
  rw [mapInv_toPNT]
  exact ⟨fun w hw => by
    rw [List.mem_map] at hw; obtain ⟨⟨p, n, t⟩, hw0, rfl⟩ := hw
    exact applyInv_rowColConst hvP hvN hrP hcN (hrc _ hw0),
   natTRestricted_inv hvP hvN k (zs.map W.toPNT) (fun w hw => ⟨(hrc w hw).1, (hrc w hw).2.1⟩) hnat⟩
lemma nodup_map_varF {l : List (Fin 9)} (h : l.Nodup) : (l.map varF).Nodup :=
  h.map fun _ _ heq => by
    by_contra hne
    exact varF_ne hne heq
lemma w9F_not_mem_map_varF (l : List (Fin 9)) : w9F ∉ l.map varF := by
  intro h; rw [List.mem_map] at h; obtain ⟨i, _, hi⟩ := h; exact w9F_ne_varF i hi.symm
def initOf (vs : List (Fin 9)) (hasW9 : Bool) : List F9 :=
  if hasW9 then vs.map varF ++ [w9F] else vs.map varF
lemma initOf_mono (vs : List (Fin 9)) (hasW9 : Bool) : ∀ w ∈ initOf vs hasW9, IsMono w := by
  intro w hw
  cases hasW9 <;> simp only [initOf, ite_true, ite_false, Bool.false_eq_true, List.mem_append, List.mem_map, List.mem_singleton] at hw
  · obtain ⟨v, _, rfl⟩ := hw; exact isMono_varF v
  · rcases hw with ⟨v, _, rfl⟩ | rfl; exact isMono_varF v; exact isMono_w9F
lemma root_input_map' (m : Nat) :
    ((initOf [0, 1, 2, 3, 4, 5, 6, 7, 8] true).map (· (maskToV m))) =
    ((List.ofFn fun (x5 : Fin 9) => m.testBit ↑x5) ++ [m.testBit 0 || m.testBit 1]) := by
  simp [initOf, List.ofFn_succ, maskToV, varF, w9F]
def checkDomAll (pos' neg' : List Nat) (v : Fin 9) (π : Fin 9 → Fin 9) (W W' : List F9) : Bool :=
  W.all fun w =>
    W'.any (fun w' => checkDom pos' neg' (permF π (projV v w)) w') ||
    checkDom pos' neg' (permF π (projV v w)) (fun _ => false)
lemma checkDomAll_ok {pos' neg' : List Nat} {v : Fin 9} {π : Fin 9 → Fin 9} {W W' : List F9}
    (h : checkDomAll pos' neg' v π W W' = true) :
    ∀ w ∈ W, (∃ w' ∈ W', dominates pos' neg' (permF π (projV v w)) w') ∨
      dominates pos' neg' (permF π (projV v w)) (fun _ => false) := by
  intro w hw
  simp only [checkDomAll, List.all_eq_true, Bool.or_eq_true, List.any_eq_true] at h
  rcases h w hw with ⟨w', hw', hd⟩ | hd
  · exact Or.inl ⟨w', hw', checkDom_ok hd⟩
  · exact Or.inr (checkDom_ok hd)
abbrev SubJust (pos neg : List Nat) (W : List F9) (pos' neg' : List Nat) (v : Fin 9) (π : Fin 9 → Fin 9) (q : Nat) : Prop :=
  SubValid pos neg v (pos'.map (pullMask π)) (neg'.map (pullMask π)) ∧
  ∀ U : List F9, (∀ u ∈ U, u ∈ W) →
    ¬ HasMono (pos'.map (pullMask π)) (neg'.map (pullMask π)) (U.map (projV v)) q
lemma mkSubJust {pos neg pos' neg' : List Nat} {W W' : List F9} {q : Nat}
    (v : Fin 9) (π : Fin 9 → Fin 9)
    (hpne : pos' ≠ []) (hnne : neg' ≠ [])
    (hp : checkSubPos pos pos' v π = true) (hn : checkSubNeg neg neg' v π = true)
    (hdom : checkDomAll pos' neg' v π W W' = true)
    (hchild : ¬ HasMono pos' neg' W' q) :
    SubValid pos neg v (pos'.map (pullMask π)) (neg'.map (pullMask π)) ∧
    ∀ U : List F9, (∀ u ∈ U, u ∈ W) →
      ¬ HasMono (pos'.map (pullMask π)) (neg'.map (pullMask π)) (U.map (projV v)) q :=
  ⟨subValid_of_checks hpne hnne hp hn, fun _ hUW => no_projV_of_child v π hUW (checkDomAll_ok hdom) hchild⟩
def checkUniqV (pos neg : List Nat) (vs : List (Fin 9)) (hasW9 : Bool) (v : Fin 9) : Bool :=
  pos.any fun e => neg.any fun m =>
    e.testBit v.1 && !m.testBit v.1 &&
    (vs.all fun u => decide (u = v) || !e.testBit u.1 || m.testBit u.1) &&
    (!hasW9 || !(e.testBit 0 || e.testBit 1) || (m.testBit 0 || m.testBit 1))
lemma uniqV_of_check {pos neg : List Nat} {vs : List (Fin 9)} {hasW9 : Bool} {v : Fin 9}
    (h : checkUniqV pos neg vs hasW9 v = true) :
    ∃ e ∈ pos, ∃ m ∈ neg, ∀ w ∈ initOf vs hasW9,
      w (maskToV e) = true → w (maskToV m) = false → w = varF v := by
  simp only [checkUniqV, List.any_eq_true, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true,
    Bool.not_eq_true', decide_eq_true_eq] at h
  obtain ⟨e, he, m, hm, ⟨⟨⟨_, _⟩, hall⟩, hw9⟩⟩ := h
  refine ⟨e, he, m, hm, fun w hw hwe hwm => ?_⟩
  cases hasW9 <;> simp only [initOf, ite_true, ite_false, Bool.false_eq_true, List.mem_append, List.mem_map, List.mem_singleton] at hw
  · obtain ⟨u, hu, rfl⟩ := hw
    rcases hall u hu with (rfl | hf) | ht
    · rfl
    · simp only [varF, maskToV] at hwe; rw [hwe] at hf; contradiction
    · simp only [varF, maskToV] at hwm; rw [hwm] at ht; contradiction
  · rcases hw with ⟨u, hu, rfl⟩ | rfl
    · rcases hall u hu with (rfl | hf) | ht
      · rfl
      · simp only [varF, maskToV] at hwe; rw [hwe] at hf; contradiction
      · simp only [varF, maskToV] at hwm; rw [hwm] at ht; contradiction
    · rcases hw9 with (hf | hf) | ht
      · contradiction
      · simp only [w9F, maskToV, Fin.val_zero, Fin.val_one] at hwe; rw [hwe] at hf; contradiction
      · simp only [w9F, maskToV, Fin.val_zero, Fin.val_one, Bool.or_eq_false_iff] at hwm
        rcases ht with ht | ht <;> simp [ht] at hwm
lemma instant_kill_fast {pos neg pos' neg' : List Nat} {vs : List (Fin 9)} {hasW9 : Bool} {W' : List F9} {k k_c : Nat}
    (v : Fin 9) (π : Fin 9 → Fin 9)
    (hpos_ne : pos ≠ []) (hneg_ne : neg ≠ [])
    (huniq : checkUniqV pos neg vs hasW9 v = true)
    (hk : k - 1 ≤ k_c)
    (hp : checkSubPos pos pos' v π = true) (hn : checkSubNeg neg neg' v π = true)
    (hpne : pos' ≠ []) (hnne : neg' ≠ [])
    (hdom : checkDomAll pos' neg' v π (initOf vs hasW9) W' = true)
    (hchild : ¬ HasMono pos' neg' W' k_c) :
    ¬ HasMono pos neg (initOf vs hasW9) k := by
  obtain ⟨e, he, m, hm, hu⟩ := uniqV_of_check huniq
  exact instant_kill v π e m hpos_ne hneg_ne (initOf_mono vs hasW9) he hm hu hk
    (checkSubPos_ok hp) (checkSubNeg_ok hn) hpne hnne (checkDomAll_ok hdom) hchild
lemma classify_U_noW9 {pos neg : List Nat} {vs : List (Fin 9)} {k : Nat} {U : List F9}
    (hnd : vs.Nodup) (hall : vs.all (checkUniqV pos neg vs false) = true)
    (hUW : ∀ u ∈ U, u ∈ initOf vs false) (hUnd : U.Nodup) (hSU : SMonoLive pos neg k U) :
    U.Perm (vs.map varF) ∧ vs.length ≤ k + 1 := by
  have hmem : ∀ x ∈ vs.map varF, x ∈ U := by
    intro x hx; rw [List.mem_map] at hx; obtain ⟨v, hv, rfl⟩ := hx
    simp only [List.all_eq_true] at hall
    obtain ⟨e, he, m, hm, hu⟩ := uniqV_of_check (hall v hv)
    obtain ⟨w, hwU, hwe, hwm⟩ := sMonoLive_covers k U hSU e he m hm
    have heq := hu w (hUW w hwU) hwe hwm
    exact heq ▸ hwU
  have hp : U.Perm (vs.map varF) := nodup_perm_of_subset hUnd (nodup_map_varF hnd) hUW hmem
  have hl := sMonoLive_len k U hSU
  have hpe := hp.length_eq; rw [List.length_map] at hpe
  exact ⟨hp, by omega⟩
lemma classify_U_w9 {pos neg : List Nat} {vs : List (Fin 9)} {k : Nat} {U : List F9}
    (hnd : vs.Nodup) (hall : vs.all (checkUniqV pos neg vs true) = true)
    (hUW : ∀ u ∈ U, u ∈ initOf vs true) (hUnd : U.Nodup) (hSU : SMonoLive pos neg k U) :
    (U.Perm (vs.map varF) ∨ U.Perm (vs.map varF ++ [w9F])) ∧ vs.length ≤ k + 1 := by
  have hmem : ∀ x ∈ vs.map varF, x ∈ U := by
    intro x hx; rw [List.mem_map] at hx; obtain ⟨v, hv, rfl⟩ := hx
    simp only [List.all_eq_true] at hall
    obtain ⟨e, he, m, hm, hu⟩ := uniqV_of_check (hall v hv)
    obtain ⟨w, hwU, hwe, hwm⟩ := sMonoLive_covers k U hSU e he m hm
    have heq := hu w (hUW w hwU) hwe hwm
    exact heq ▸ hwU
  have hp : U.Perm (vs.map varF) ∨ U.Perm (vs.map varF ++ [w9F]) :=
    nodup_perm_or_cons hUnd (nodup_map_varF hnd) (w9F_not_mem_map_varF vs)
      (fun x hx => by have := hUW x hx; simpa [initOf] using this) hmem
  have hl := sMonoLive_len k U hSU
  have hlen : vs.length ≤ U.length := by
    rcases hp with h | h <;> have hpe := h.length_eq <;> simp at hpe <;> omega
  exact ⟨hp, by omega⟩
def encTagged (pos neg : List Nat) (Wt : List (F9 × Nat)) : List (Nat × Nat × Nat) :=
  Wt.map fun wt => (encPos pos neg.length wt.1, encNeg pos.length neg wt.1, wt.2)
def mkWt (vs : List (Fin 9)) (tgs : List Nat) (hasW9 : Bool) : List (F9 × Nat) :=
  vs.zipWith (fun v t => (varF v, t)) tgs ++ (if hasW9 then [(w9F, 0)] else [])
lemma zipWith_varF_mono : ∀ (vs : List (Fin 9)) (tgs : List Nat),
    ∀ wt ∈ vs.zipWith (fun v t => (varF v, t)) tgs, IsMono wt.1
  | [], _, _, h => by simp at h
  | _, [], _, h => by simp at h
  | v :: vs, t :: tgs, wt, h => by
    simp only [List.zipWith_cons_cons, List.mem_cons] at h
    rcases h with rfl | h
    · exact isMono_varF v
    · exact zipWith_varF_mono vs tgs wt h
lemma mkWt_mono (vs : List (Fin 9)) (tgs : List Nat) (hasW9 : Bool) :
    ∀ wt ∈ mkWt vs tgs hasW9, IsMono wt.1 := by
  intro wt hwt
  rcases List.mem_append.1 hwt with h1 | h2
  · exact zipWith_varF_mono vs tgs wt h1
  · cases hasW9 <;> simp at h2; subst h2; exact isMono_w9F
def checkMasks (P N m1 m2 m4 m8 rs : Nat) : Bool :=
  checkMaskLo P N 1 m1 && checkMaskLo P N 2 m2 && checkMaskLo P N 4 m4 && checkMaskLo P N 8 m8 &&
  checkRowStart P N rs
def mkLitWt (top : Nat) (lits : List (Nat × Nat)) (tgs : List Nat) (withW9 : Bool) : List W :=
  lits.zipWith (fun pn t => ⟨pn.1, pn.2, t, Nat.land pn.1 (Nat.xor pn.2 top)⟩) (if withW9 then tgs ++ [0] else tgs)
lemma zipWith_mkW_wOk (top : Nat) : ∀ (l1 : List (Nat × Nat)) (l2 : List Nat),
    WOk top (l1.zipWith (fun pn t => ⟨pn.1, pn.2, t, Nat.land pn.1 (Nat.xor pn.2 top)⟩) l2)
  | [], _ => wOk_nil
  | _ :: _, [] => wOk_nil
  | _ :: xs, _ :: ys => wOk_cons rfl (zipWith_mkW_wOk top xs ys)
lemma zipWith_mkW_toPNT (top : Nat) : ∀ (l1 : List (Nat × Nat)) (l2 : List Nat),
    (l1.zipWith (fun pn t => (⟨pn.1, pn.2, t, Nat.land pn.1 (Nat.xor pn.2 top)⟩ : W)) l2).map W.toPNT =
    l1.zipWith (fun pn t => (pn.1, pn.2, t)) l2
  | [], _ => rfl
  | _ :: _, [] => rfl
  | _ :: xs, _ :: ys => by simp only [List.zipWith_cons_cons, List.map_cons, W.toPNT, zipWith_mkW_toPNT top xs ys]
lemma zipWith_enc_eq : ∀ (vs : List (Fin 9)) (tgs : List Nat) (pos neg : List Nat),
    (vs.zipWith (fun v t => (varF v, t)) tgs).map (fun wt => (encPos pos neg.length wt.1, encNeg pos.length neg wt.1, wt.2)) =
    (vs.map fun v => (encPos pos neg.length (varF v), encNeg pos.length neg (varF v))).zipWith (fun pn t => (pn.1, pn.2, t)) tgs
  | [], _, _, _ => rfl
  | _ :: _, [], _, _ => rfl
  | _ :: vs, _ :: tgs, pos, neg => by
    simp only [List.zipWith_cons_cons, List.map_cons, zipWith_enc_eq vs tgs pos neg]
lemma zipWith_append_left {α β γ : Type} (f : α → β → γ) :
    ∀ (l1 l1' : List α) (l2 : List β), l1.length = l2.length →
      (l1 ++ l1').zipWith f l2 = l1.zipWith f l2
  | [], _, [], _ => by simp
  | [], _, _ :: _, h => by simp at h
  | _ :: _, _, [], h => by simp at h
  | _ :: xs, l1', _ :: ys, h => by
    simp only [List.cons_append, List.zipWith_cons_cons, zipWith_append_left f xs l1' ys (by simpa using h)]
lemma zipWith_append_both {α β γ : Type} (f : α → β → γ) :
    ∀ (l1 : List α) (l2 : List β) (a : α) (b : β), l1.length = l2.length →
      (l1 ++ [a]).zipWith f (l2 ++ [b]) = l1.zipWith f l2 ++ [f a b]
  | [], [], _, _, _ => rfl
  | [], _ :: _, _, _, h => by simp at h
  | _ :: _, [], _, _, h => by simp at h
  | _ :: xs, _ :: ys, a, b, h => by
    simp only [List.cons_append, List.zipWith_cons_cons, zipWith_append_both f xs ys a b (by simpa using h)]
lemma encTagged_eq_mkLitWt {pos neg : List Nat} {top : Nat} {vs : List (Fin 9)} {tgs : List Nat} {hasW9 withW9 : Bool} {lits : List (Nat × Nat)}
    (hl : vs.length = tgs.length) (hw : withW9 = true → hasW9 = true)
    (heq : (initOf vs hasW9).map (fun f => (encPos pos neg.length f, encNeg pos.length neg f)) = lits) :
    encTagged pos neg (mkWt vs tgs withW9) = (mkLitWt top lits tgs withW9).map W.toPNT := by
  subst heq
  rw [mkLitWt, zipWith_mkW_toPNT]
  cases withW9
  · cases hasW9
    · simp only [encTagged, mkWt, initOf, Bool.false_eq_true, ite_false, List.append_nil, List.map_map]
      exact zipWith_enc_eq vs tgs pos neg
    · simp only [encTagged, mkWt, initOf, Bool.false_eq_true, ite_false, ite_true, List.append_nil, List.map_append, List.map_map]
      rw [zipWith_enc_eq vs tgs pos neg]
      exact (zipWith_append_left _ _ _ _ (by rw [List.length_map]; exact hl)).symm
  · have h9 := hw rfl; subst h9
    simp only [encTagged, mkWt, initOf, ite_true, List.map_append, List.map_cons, List.map_nil, List.map_map]
    rw [zipWith_enc_eq vs tgs pos neg]
    have hlen : (vs.map fun v => (encPos pos neg.length (varF v), encNeg pos.length neg (varF v))).length = tgs.length := by
      rw [List.length_map]; exact hl
    exact (zipWith_append_both (fun pn t => (pn.1, pn.2, t)) _ _ (encPos pos neg.length w9F, encNeg pos.length neg w9F) 0 hlen).symm
lemma close_dir_case {pos neg : List Nat} {top m1 m2 m4 m8 rowStart rowFull k : Nat}
    {vs : List (Fin 9)} {tgs : List Nat} {hasW9 withW9 : Bool} {lits : List (Nat × Nat)}
    (hP : 0 < pos.length) (hN : 0 < neg.length) (hrf : rowFull = (1 <<< neg.length) - 1)
    (htop : 2 ^ (pos.length * neg.length) - 1 = top)
    (hms : checkMasks pos.length neg.length m1 m2 m4 m8 rowStart = true)
    (hl : vs.length = tgs.length) (hw : withW9 = true → hasW9 = true)
    (heq : (initOf vs hasW9).map (fun f => (encPos pos neg.length f, encNeg pos.length neg f)) = lits)
    (htags : ∀ wt ∈ mkWt vs tgs withW9, TagOk pos neg ((mkWt vs tgs withW9).map Prod.fst) k wt.1 wt.2)
    (hS : SMonoLive pos neg k ((mkWt vs tgs withW9).map Prod.fst))
    (hdir : searchCert top neg.length m1 m2 m4 m8 rowStart rowFull (fun _ _ => false) k (mkLitWt top lits tgs withW9) = false) :
    False := by
  simp only [checkMasks, Bool.and_eq_true] at hms
  obtain ⟨⟨⟨⟨hm1, hm2⟩, hm4⟩, hm8⟩, hrs⟩ := hms
  have hnat := sMonoLive_to_nat hP hN k (mkWt vs tgs withW9) (mkWt_mono vs tgs withW9) htags hS
  have hrc : ∀ w ∈ encTagged pos neg (mkWt vs tgs withW9), RowColConst pos.length neg.length w.1 w.2.1 := by
    intro w hw; rw [encTagged, List.mem_map] at hw; obtain ⟨wt, _, rfl⟩ := hw
    exact enc_rowColConst pos neg hP hN wt.1
  have hm_eq := encTagged_eq_mkLitWt (top := top) hl hw heq
  change NatTRestricted (2 ^ (pos.length * neg.length) - 1) k (encTagged pos neg (mkWt vs tgs withW9)) at hnat
  rw [hm_eq] at hnat hrc
  have hok : WOk (2 ^ (pos.length * neg.length) - 1) (mkLitWt top lits tgs withW9) := by
    rw [htop]; exact zipWith_mkW_wOk top _ _
  have hdir' : searchCert (2 ^ (pos.length * neg.length) - 1) neg.length m1 m2 m4 m8 rowStart rowFull (fun _ _ => false) k (mkLitWt top lits tgs withW9) = false := by
    rw [htop]; exact hdir
  exact direct_impossible hN hrf (checkRowStart_ok hrs)
    (checkMaskLo_ok hm1) (checkMaskLo_ok hm2) (checkMaskLo_ok hm4) (checkMaskLo_ok hm8)
    hdir' hok hrc hnat
lemma close_ht_case {pos neg : List Nat} {top m1 m2 m4 m8 rowStart rowFull cap k : Nat}
    {cnt : Nat → Nat} {decSt : Nat → Nat → List W}
    {certHit : Nat → List W → Bool}
    {vs : List (Fin 9)} {tgs : List Nat} {hasW9 withW9 : Bool} {lits : List (Nat × Nat)}
    (hP : 0 < pos.length) (hN : 0 < neg.length) (hrf : rowFull = (1 <<< neg.length) - 1)
    (htop : 2 ^ (pos.length * neg.length) - 1 = top)
    (hms : checkMasks pos.length neg.length m1 m2 m4 m8 rowStart = true)
    (hl : vs.length = tgs.length) (hw : withW9 = true → hasW9 = true)
    (heq : (initOf vs hasW9).map (fun f => (encPos pos neg.length f, encNeg pos.length neg f)) = lits)
    (hdec_ok : ∀ s idx, WOk (2 ^ (pos.length * neg.length) - 1) (decSt s idx))
    (hcert_sound : ∀ s zs, (∀ w ∈ zs.map W.toPNT, RowColConst pos.length neg.length w.1 w.2.1) →
      NatTRestricted (2 ^ (pos.length * neg.length) - 1) s (zs.map W.toPNT) → certHit s zs = true →
      ∃ idx < cnt s, (∀ w ∈ (decSt s idx).map W.toPNT, RowColConst pos.length neg.length w.1 w.2.1) ∧
        NatTRestricted (2 ^ (pos.length * neg.length) - 1) s ((decSt s idx).map W.toPNT))
    (hcheck : ∀ s ≤ cap, ∀ idx < cnt s,
      stepExpand (2 ^ (pos.length * neg.length) - 1) neg.length m1 m2 m4 m8 rowStart rowFull certHit s (decSt s idx) = false)
    (hk : k ≤ cap)
    (htags : ∀ wt ∈ mkWt vs tgs withW9, TagOk pos neg ((mkWt vs tgs withW9).map Prod.fst) k wt.1 wt.2)
    (hS : SMonoLive pos neg k ((mkWt vs tgs withW9).map Prod.fst))
    (hroot : searchCert top neg.length m1 m2 m4 m8 rowStart rowFull certHit k (mkLitWt top lits tgs withW9) = false) :
    False := by
  simp only [checkMasks, Bool.and_eq_true] at hms
  obtain ⟨⟨⟨⟨hm1, hm2⟩, hm4⟩, hm8⟩, hrs⟩ := hms
  have hnat := sMonoLive_to_nat hP hN k (mkWt vs tgs withW9) (mkWt_mono vs tgs withW9) htags hS
  have hrc : ∀ w ∈ encTagged pos neg (mkWt vs tgs withW9), RowColConst pos.length neg.length w.1 w.2.1 := by
    intro w hw; rw [encTagged, List.mem_map] at hw; obtain ⟨wt, _, rfl⟩ := hw
    exact enc_rowColConst pos neg hP hN wt.1
  have hm_eq := encTagged_eq_mkLitWt (top := top) hl hw heq
  change NatTRestricted (2 ^ (pos.length * neg.length) - 1) k (encTagged pos neg (mkWt vs tgs withW9)) at hnat
  rw [hm_eq] at hnat hrc
  have hok : WOk (2 ^ (pos.length * neg.length) - 1) (mkLitWt top lits tgs withW9) := by
    rw [htop]; exact zipWith_mkW_wOk top _ _
  have hroot' : searchCert (2 ^ (pos.length * neg.length) - 1) neg.length m1 m2 m4 m8 rowStart rowFull certHit k (mkLitWt top lits tgs withW9) = false := by
    rw [htop]; exact hroot
  exact root_impossible hN hrf (checkRowStart_ok hrs)
    (checkMaskLo_ok hm1) (checkMaskLo_ok hm2) (checkMaskLo_ok hm4) (checkMaskLo_ok hm8)
    hdec_ok hcert_sound cap hcheck hk hroot' hok hrc hnat
lemma tags_zero_ok {pos neg : List Nat} {W : List F9} {k : Nat} {Wt : List (F9 × Nat)}
    (h : Wt.all (fun wt => Nat.beq wt.2 0) = true) :
    ∀ wt ∈ Wt, TagOk pos neg W k wt.1 wt.2 := by
  intro wt hwt
  simp only [List.all_eq_true, Nat.beq_eq] at h
  rw [h wt hwt]; trivial
lemma tagOk_of_sub {pos neg pos' neg' : List Nat} {W U : List F9} {k q t : Nat} {v : Fin 9} {π : Fin 9 → Fin 9}
    (hsub : SubValid pos neg v (pos'.map (pullMask π)) (neg'.map (pullMask π)) ∧
      ∀ U0 : List F9, (∀ u ∈ U0, u ∈ W) → ¬ HasMono (pos'.map (pullMask π)) (neg'.map (pullMask π)) (U0.map (projV v)) q)
    (hUW : ∀ u ∈ U, u ∈ W) (ht : (t = 1 ∧ k ≤ q + 3) ∨ (t = 2 ∧ k ≤ q + 2)) :
    TagOk pos neg U k (varF v) t := by
  have hzv : projV v (varF v) = fun _ => false := by funext x; simp [projV, varF]
  rcases ht with ⟨rfl, hle⟩ | ⟨rfl, hle⟩
  · exact ⟨v, _, _, hsub.1, hzv, fun m hm hhm => hsub.2 U hUW (hasMono_mono_k (by omega) hhm)⟩
  · exact ⟨v, _, _, hsub.1, hzv, fun m hm hhm => hsub.2 U hUW (hasMono_mono_k (by omega) hhm)⟩

-- S3 (V=6, P=6, N=5, w9=0, k=7)
def pos_S3 : List Nat := [12, 132, 160, 264, 288, 320]
def neg_S3 : List Nat := [100, 104, 200, 260, 384]
def vs_S3 : List (Fin 9) := [2, 3, 5, 6, 7, 8]
def top_S3 : Nat := 0x3fffffff
def m1_S3 : Nat := 0x1ef7bdef
def m2_S3 : Nat := 0xe739ce7
def m4_S3 : Nat := 0x2108421
def m8_S3 : Nat := 0
def rs_S3 : Nat := 0x2108421
def rf_S3 : Nat := 31
def litW_S3 : List (Nat × Nat) := [(0x3ff, 0x1294a529), (0xf801f, 0xc6318c6), (0x1f07c00, 0x6318c63), (0x3e000000, 0xe739ce7), (0x7fe0, 0x294a5294), (0x3fff8000, 0x318c6318)]
lemma encLit_S3 : (initOf vs_S3 false).map (fun f => (encPos pos_S3 neg_S3.length f, encNeg pos_S3.length neg_S3 f)) = litW_S3 := by decide +kernel
lemma r_S3_0 : searchCert top_S3 5 m1_S3 m2_S3 m4_S3 m8_S3 rs_S3 rf_S3 (fun _ _ => false) 5 (mkLitWt top_S3 litW_S3 [0, 0, 0, 0, 0, 0] false) = false := by decide +kernel
lemma r_S3_1 : searchCert top_S3 5 m1_S3 m2_S3 m4_S3 m8_S3 rs_S3 rf_S3 (fun _ _ => false) 6 (mkLitWt top_S3 litW_S3 [0, 0, 0, 0, 0, 0] false) = false := by decide +kernel
lemma r_S3_2 : searchCert top_S3 5 m1_S3 m2_S3 m4_S3 m8_S3 rs_S3 rf_S3 (fun _ _ => false) 7 (mkLitWt top_S3 litW_S3 [0, 0, 0, 0, 0, 0] false) = false := by decide +kernel
lemma no_S3 : ¬ HasMono pos_S3 neg_S3 (initOf vs_S3 false) 7 := by
  have htop : 2 ^ (pos_S3.length * neg_S3.length) - 1 = top_S3 := by decide +kernel
  have hms : checkMasks pos_S3.length neg_S3.length m1_S3 m2_S3 m4_S3 m8_S3 rs_S3 = true := by decide +kernel
  intro h
  obtain ⟨k1, hk1, hm1⟩ := hasMono_to_monoLive (by decide) (by decide) 7 _ h
  obtain ⟨k2, hk2, U, hUW, hUnd, hSU⟩ := monoLive_to_sMonoLive k1 _ hm1
  obtain ⟨hperm, hlen⟩ := classify_U_noW9 (by decide) (by decide +kernel) hUW hUnd hSU
  have hk_min : 5 ≤ k2 := by simp [vs_S3] at hlen; omega
  have hk_le : k2 ≤ 7 := by omega
  interval_cases k2
  ·
    exact close_dir_case (vs := vs_S3) (tgs := [0, 0, 0, 0, 0, 0]) (withW9 := false) (by decide) (by decide) (by decide) htop hms (by decide) (by decide) encLit_S3 (tags_zero_ok (by decide)) (sMonoLive_perm hperm hSU) r_S3_0
  ·
    exact close_dir_case (vs := vs_S3) (tgs := [0, 0, 0, 0, 0, 0]) (withW9 := false) (by decide) (by decide) (by decide) htop hms (by decide) (by decide) encLit_S3 (tags_zero_ok (by decide)) (sMonoLive_perm hperm hSU) r_S3_1
  ·
    exact close_dir_case (vs := vs_S3) (tgs := [0, 0, 0, 0, 0, 0]) (withW9 := false) (by decide) (by decide) (by decide) htop hms (by decide) (by decide) encLit_S3 (tags_zero_ok (by decide)) (sMonoLive_perm hperm hSU) r_S3_2

-- S4 (V=6, P=6, N=5, w9=0, k=7)
def pos_S4 : List Nat := [6, 66, 132, 160, 288, 320]
def neg_S4 : List Nat := [34, 100, 192, 260, 386]
def vs_S4 : List (Fin 9) := [1, 2, 5, 6, 7, 8]
def top_S4 : Nat := 0x3fffffff
def m1_S4 : Nat := 0x1ef7bdef
def m2_S4 : Nat := 0xe739ce7
def m4_S4 : Nat := 0x2108421
def m8_S4 : Nat := 0
def rs_S4 : Nat := 0x2108421
def rf_S4 : Nat := 31
def litW_S4 : List (Nat × Nat) := [(0x3ff, 0x2318c631), (0x7c1f, 0x14a5294a), (0x1ff8000, 0x6318c63), (0x3e0003e0, 0xc6318c6), (0xffc00, 0x294a5294), (0x3ff00000, 0x318c6318)]
lemma encLit_S4 : (initOf vs_S4 false).map (fun f => (encPos pos_S4 neg_S4.length f, encNeg pos_S4.length neg_S4 f)) = litW_S4 := by decide +kernel
lemma r_S4_0 : searchCert top_S4 5 m1_S4 m2_S4 m4_S4 m8_S4 rs_S4 rf_S4 (fun _ _ => false) 5 (mkLitWt top_S4 litW_S4 [0, 0, 0, 0, 0, 0] false) = false := by decide +kernel
lemma r_S4_1 : searchCert top_S4 5 m1_S4 m2_S4 m4_S4 m8_S4 rs_S4 rf_S4 (fun _ _ => false) 6 (mkLitWt top_S4 litW_S4 [0, 0, 0, 0, 0, 0] false) = false := by decide +kernel
lemma r_S4_2 : searchCert top_S4 5 m1_S4 m2_S4 m4_S4 m8_S4 rs_S4 rf_S4 (fun _ _ => false) 7 (mkLitWt top_S4 litW_S4 [0, 0, 0, 0, 0, 0] false) = false := by decide +kernel
lemma no_S4 : ¬ HasMono pos_S4 neg_S4 (initOf vs_S4 false) 7 := by
  have htop : 2 ^ (pos_S4.length * neg_S4.length) - 1 = top_S4 := by decide +kernel
  have hms : checkMasks pos_S4.length neg_S4.length m1_S4 m2_S4 m4_S4 m8_S4 rs_S4 = true := by decide +kernel
  intro h
  obtain ⟨k1, hk1, hm1⟩ := hasMono_to_monoLive (by decide) (by decide) 7 _ h
  obtain ⟨k2, hk2, U, hUW, hUnd, hSU⟩ := monoLive_to_sMonoLive k1 _ hm1
  obtain ⟨hperm, hlen⟩ := classify_U_noW9 (by decide) (by decide +kernel) hUW hUnd hSU
  have hk_min : 5 ≤ k2 := by simp [vs_S4] at hlen; omega
  have hk_le : k2 ≤ 7 := by omega
  interval_cases k2
  ·
    exact close_dir_case (vs := vs_S4) (tgs := [0, 0, 0, 0, 0, 0]) (withW9 := false) (by decide) (by decide) (by decide) htop hms (by decide) (by decide) encLit_S4 (tags_zero_ok (by decide)) (sMonoLive_perm hperm hSU) r_S4_0
  ·
    exact close_dir_case (vs := vs_S4) (tgs := [0, 0, 0, 0, 0, 0]) (withW9 := false) (by decide) (by decide) (by decide) htop hms (by decide) (by decide) encLit_S4 (tags_zero_ok (by decide)) (sMonoLive_perm hperm hSU) r_S4_1
  ·
    exact close_dir_case (vs := vs_S4) (tgs := [0, 0, 0, 0, 0, 0]) (withW9 := false) (by decide) (by decide) (by decide) htop hms (by decide) (by decide) encLit_S4 (tags_zero_ok (by decide)) (sMonoLive_perm hperm hSU) r_S4_2

-- S2 (V=7, P=8, N=7, w9=0, k=10)
def pos_S2 : List Nat := [6, 12, 66, 132, 160, 264, 288, 320]
def neg_S2 : List Nat := [42, 100, 104, 138, 200, 260, 386]
def vs_S2 : List (Fin 9) := [1, 2, 3, 5, 6, 7, 8]
def top_S2 : Nat := 0xffffffffffffff
def m1_S2 : Nat := 0x7efdfbf7efdfbf
def m2_S2 : Nat := 0x3e7cf9f3e7cf9f
def m4_S2 : Nat := 0xe1c3870e1c387
def m8_S2 : Nat := 0
def rs_S2 : Nat := 0x2040810204081
def rf_S2 : Nat := 127
def litW_S2 : List (Nat × Nat) := [(0x1fc07f, 0x93264c993264c9), (0xfe03fff, 0x44891224489122), (0x3f800003f80, 0x3a74e9d3a74e9d), (0x1fc07f0000000, 0xe1c3870e1c387), (0xfe0000001fc000, 0x2c58b162c58b16), (0x7ffe00000, 0xb162c58b162c58), (0xfffff800000000, 0xc183060c183060)]
lemma encLit_S2 : (initOf vs_S2 false).map (fun f => (encPos pos_S2 neg_S2.length f, encNeg pos_S2.length neg_S2 f)) = litW_S2 := by decide +kernel
def pi_S2_1 : Fin 9 → Fin 9 := fun i : Fin 9 => (match i.1 with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8 : Fin 9)
lemma sub_S2_1 : SubJust pos_S2 neg_S2 (initOf vs_S2 false) pos_S3 neg_S3 1 pi_S2_1 7 :=
  mkSubJust 1 pi_S2_1 (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) no_S3
def pi_S2_3 : Fin 9 → Fin 9 := fun i : Fin 9 => (match i.1 with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8 : Fin 9)
lemma sub_S2_3 : SubJust pos_S2 neg_S2 (initOf vs_S2 false) pos_S4 neg_S4 3 pi_S2_3 7 :=
  mkSubJust 3 pi_S2_3 (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) no_S4
def pi_S2_5 : Fin 9 → Fin 9 := fun i : Fin 9 => (match i.1 with | 0 => 0 | 1 => 3 | 2 => 8 | 3 => 5 | 4 => 1 | 5 => 4 | 6 => 2 | 7 => 6 | _ => 7 : Fin 9)
lemma sub_S2_5 : SubJust pos_S2 neg_S2 (initOf vs_S2 false) pos_S3 neg_S3 5 pi_S2_5 7 :=
  mkSubJust 5 pi_S2_5 (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) no_S3
def pi_S2_6 : Fin 9 → Fin 9 := fun i : Fin 9 => (match i.1 with | 0 => 0 | 1 => 6 | 2 => 8 | 3 => 3 | 4 => 1 | 5 => 7 | 6 => 4 | 7 => 5 | _ => 2 : Fin 9)
lemma sub_S2_6 : SubJust pos_S2 neg_S2 (initOf vs_S2 false) pos_S3 neg_S3 6 pi_S2_6 7 :=
  mkSubJust 6 pi_S2_6 (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) no_S3
def pi_S2_7 : Fin 9 → Fin 9 := fun i : Fin 9 => (match i.1 with | 0 => 0 | 1 => 2 | 2 => 7 | 3 => 5 | 4 => 1 | 5 => 6 | 6 => 3 | 7 => 4 | _ => 8 : Fin 9)
lemma sub_S2_7 : SubJust pos_S2 neg_S2 (initOf vs_S2 false) pos_S3 neg_S3 7 pi_S2_7 7 :=
  mkSubJust 7 pi_S2_7 (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) no_S3
def wp_S2 (i : Nat) : Nat := (bn (Nat.blt i 1) 0xfe0007ffffc07f000007ffffc07fffffffffe03ffffe0007ffffc000fffff800003f800000000000007f000007ffe0007f0000000fe03ffffffff80fe03ffffffff800000000000007ffe00000000000001fc07f0003f800003f80fe0000001fc00001fc07f00000000000000fe0007f 0xffffffffe03f80fe0000001fc07ffffff8001fc000fffff8001fc07ffe0007ffffffff00000000003fff0003ffffe03f800003f80fe03fffffffffffffc07fffffffffe00000000007ffe03fff0003ffffffffff)
def wn_S2 (i : Nat) : Nat := (bn (Nat.blt i 1) 0xbf7efdfbf7efdfb366cd9b366cd9f5ebd7af5ebd7abd7af5ebd7af5efbf7efdfbf7efd04081020408102b162c58b162c5844891224489122c58b162c58b162c183060c183060b162c58b162c5893264c993264c93a74e9d3a74e9d2c58b162c58b160e1c3870e1c38700000000000000 0xfbf7efdfbf7efdbf7efdfbf7efdfeddbb76eddbb76d3a74e9d3a74e9fdfbf7efdfbf7e00000000000000bb76eddbb76edd7efdfbf7efdfbff3e7cf9f3e7cf9f1e3c78f1e3c78f5ebd7af5ebd7abb76eddbb76edd)
def fixP_S2_1 : Nat := 0
def swP_S2_1 : List (Nat × Nat) := [(0x1fc000, 14), (0xfe03f80, 28), (0x7f, 42)]
def fixN_S2_1 : Nat := 0x62c58b162c58b1
def swN_S2_1 : List (Nat × Nat) := [(0x8102040810204, 1), (0x4081020408102, 5)]
def fixP_S2_2 : Nat := 0x7f01fc000
def swP_S2_2 : List (Nat × Nat) := [(0xfe00000, 21), (0x3f80, 28), (0x7f, 49)]
def fixN_S2_2 : Nat := 0x40810204081020
def swN_S2_2 : List (Nat × Nat) := [(0x8102040810204, 1), (0x2040810204081, 4), (0x4081020408102, 5)]
def fixP_S2_3 : Nat := 0x3f800003f80
def swP_S2_3 : List (Nat × Nat) := [(0x1fc0000000000, 7), (0x1fc000, 14), (0x7f, 21)]
def fixN_S2_3 : Nat := 0xddbb76eddbb76e
def swN_S2_3 : List (Nat × Nat) := [(0x2040810204081, 4)]
def st_S2_7 (_ : Nat) : Nat := 0x61212403448573860b121a242808
def htd_S2_7 (_ : Nat) : Nat := 0
def hta_S2_7 (_ : Nat) : Nat := 0x50010800
def st_S2_8 (_ : Nat) : Nat := 0x2218a84500e1216004831508a01c242c00d860b11403848580180c682a8068a0b0032602a4900d1416004830c08a01a282c00b860b11403450580120e1622806890b000c1524807090b620018a8588d040242c009860b12403448580120c3824806890b070c382c4900d121640182c4900d121404008861c1240344858006201624807090b000c3c2c4900d1416001860e09201a282c006860b11403448583861816228068a0b200c15248068a0aa2002c38548a01c242c0030549201a243288
def htd_S2_8 (_ : Nat) : Nat := 0x80d0204000000c400000058000380800800300
def hta_S2_8 (_ : Nat) : Nat := 0xa4d12000289908e16800000006006c03112f41bf6014a3c01186b5b2aa053982e6803084b457c3c0009e0000001092000000000a128e8026000002a940110002080014800000700000002a80
def st_S2_9 (_ : Nat) : Nat := 0x8860b114034485831a0a924034505830c0b11403450589060b11403448583150b114038485830e0b124034485830548d040384858
def htd_S2_9 (_ : Nat) : Nat := 0x847
def hta_S2_9 (_ : Nat) : Nat := 0x28960d2799500008ee6ea81e0831a1302c0
def st_S2_10 (_ : Nat) : Nat := 0x60a9140344857
def htd_S2_10 (_ : Nat) : Nat := 0
def hta_S2_10 (_ : Nat) : Nat := 0x2
def decW_S2 (e : Nat) : W :=
  let s := Nat.shiftRight e 2; let c := Nat.shiftRight s 4; let off := Nat.mul (Nat.land s 15) 56
  let p := Nat.land (Nat.shiftRight (wp_S2 c) off) top_S2; let n := Nat.land (Nat.shiftRight (wn_S2 c) off) top_S2
  ⟨p, n, Nat.land e 3, Nat.land p (Nat.xor n top_S2)⟩
def decWList_S2 : Nat → Nat → List W
  | 0, _ => []
  | n + 1, raw => decW_S2 (Nat.land raw 127) :: decWList_S2 n (Nat.shiftRight raw 7)
lemma decWList_S2_ok : ∀ n raw, WOk top_S2 (decWList_S2 n raw)
  | 0, _ => wOk_nil
  | n + 1, raw => wOk_cons rfl (decWList_S2_ok n _)
def cnt_S2 (k : Nat) : Nat := (bn (Nat.blt k 9) (bn (Nat.blt k 8) (bn (Nat.beq k 7) (2) 0) (bn (Nat.beq k 8) (23) 0)) (bn (Nat.blt k 10) (bn (Nat.beq k 9) (7) 0) (bn (Nat.beq k 10) (1) 0)))
def decSt_S2 (k idx : Nat) : List W := (match Nat.blt k 9 with | true => (match Nat.blt k 8 with | true => (match Nat.beq k 7 with | true => (stProbe 60 st_S2_7 decWList_S2 idx) | false => []) | false => (match Nat.beq k 8 with | true => (stProbe 67 st_S2_8 decWList_S2 idx) | false => [])) | false => (match Nat.blt k 10 with | true => (match Nat.beq k 9 with | true => (stProbe 60 st_S2_9 decWList_S2 idx) | false => []) | false => (match Nat.beq k 10 with | true => (stProbe 53 st_S2_10 decWList_S2 idx) | false => [])))
lemma decSt_S2_ok (s idx : Nat) : WOk (2 ^ (8 * 7) - 1) (decSt_S2 s idx) := by
  have htop : (2 ^ (8 * 7) - 1) = top_S2 := by decide +kernel
  rw [htop]; unfold decSt_S2; repeat (first | apply wOk_match | exact wOk_nil | exact decWList_S2_ok _ _)
def lookup_S2 (k : Nat) (zs : List W) : Nat := (match Nat.blt k 9 with | true => (match Nat.blt k 8 with | true => (match Nat.beq k 7 with | true => (htProbe 1 1 7 9 4 15 4 15 htd_S2_7 hta_S2_7 zs) | false => 0) | false => (match Nat.beq k 8 with | true => (htProbe 1 23 31 89 7 127 7 127 htd_S2_8 hta_S2_8 zs) | false => 0)) | false => (match Nat.blt k 10 with | true => (match Nat.beq k 9 with | true => (htProbe 1 6 31 28 5 31 5 31 htd_S2_9 hta_S2_9 zs) | false => 0) | false => (match Nat.beq k 10 with | true => (htProbe 1 1 1 5 3 7 1 1 htd_S2_10 hta_S2_10 zs) | false => 0)))
def applyG_S2 (g : Nat) (zs : List W) : List W := match g with
  | 1 => mapInv fixP_S2_1 swP_S2_1 fixN_S2_1 swN_S2_1 zs
  | 2 => mapInv fixP_S2_2 swP_S2_2 fixN_S2_2 swN_S2_2 zs
  | 3 => mapInv fixP_S2_3 swP_S2_3 fixN_S2_3 swN_S2_3 zs
  | _ => zs
lemma applyG_S2_sound (g s : Nat) (zs : List W)
    (hrc : ∀ w ∈ zs.map W.toPNT, RowColConst 8 7 w.1 w.2.1)
    (hnat : NatTRestricted (2 ^ (8 * 7) - 1) s (zs.map W.toPNT)) :
    (∀ w ∈ (applyG_S2 g zs).map W.toPNT, RowColConst 8 7 w.1 w.2.1) ∧ NatTRestricted (2 ^ (8 * 7) - 1) s ((applyG_S2 g zs).map W.toPNT) := by
  rcases g with _ | _ | _ | _ | g
  · exact ⟨hrc, hnat⟩
  · exact inv_list_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) hrc hnat
  · exact inv_list_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) hrc hnat
  · exact inv_list_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) hrc hnat
  · exact ⟨hrc, hnat⟩
def certHit_S2 (k : Nat) (zs : List W) : Bool :=
  let code := lookup_S2 k zs
  match Nat.beq code 0 with | true => false | false => let c := Nat.sub code 1; let q := Nat.shiftRight c 2; match Nat.blt q (cnt_S2 k) with | false => false | true => isPermW (applyG_S2 (Nat.land c 3) zs) (decSt_S2 k q)
lemma certHit_S2_sound (s : Nat) (zs : List W)
    (hrc : ∀ w ∈ zs.map W.toPNT, RowColConst 8 7 w.1 w.2.1)
    (hnat : NatTRestricted (2 ^ (8 * 7) - 1) s (zs.map W.toPNT)) (hhit : certHit_S2 s zs = true) :
    ∃ idx < cnt_S2 s, (∀ w ∈ (decSt_S2 s idx).map W.toPNT, RowColConst 8 7 w.1 w.2.1) ∧ NatTRestricted (2 ^ (8 * 7) - 1) s ((decSt_S2 s idx).map W.toPNT) := by
  unfold certHit_S2 at hhit; dsimp only at hhit
  cases h0 : Nat.beq (lookup_S2 s zs) 0 <;> simp only [h0] at hhit
  · cases h1 : Nat.blt (Nat.shiftRight (Nat.sub (lookup_S2 s zs) 1) 2) (cnt_S2 s) <;> simp only [h1] at hhit
    · contradiction
    · have hp := isPermW_sound hhit
      have ⟨h1a, h2a⟩ := applyG_S2_sound (Nat.land (Nat.sub (lookup_S2 s zs) 1) 3) s zs hrc hnat
      exact ⟨_, by simpa [Nat.blt_eq] using h1, fun w hw => h1a w (hp.mem_iff.2 hw), natTRestricted_perm hp h2a⟩
  · contradiction
def chk_S2 (k idx : Nat) : Bool :=
  match stepExpand top_S2 7 m1_S2 m2_S2 m4_S2 m8_S2 rs_S2 rf_S2 certHit_S2 k (decSt_S2 k idx) with | true => false | false => true
lemma c_S2_7_0 : span (chk_S2 7) 2 0 = true := by decide +kernel
lemma all_S2_7 : ∀ i, 0 ≤ i → i < 2 → chk_S2 7 i = true := sr rfl c_S2_7_0
lemma c_S2_8_0 : span (chk_S2 8) 23 0 = true := by decide +kernel
lemma all_S2_8 : ∀ i, 0 ≤ i → i < 23 → chk_S2 8 i = true := sr rfl c_S2_8_0
lemma c_S2_9_0 : span (chk_S2 9) 7 0 = true := by decide +kernel
lemma all_S2_9 : ∀ i, 0 ≤ i → i < 7 → chk_S2 9 i = true := sr rfl c_S2_9_0
lemma c_S2_10_0 : span (chk_S2 10) 1 0 = true := by decide +kernel
lemma all_S2_10 : ∀ i, 0 ≤ i → i < 1 → chk_S2 10 i = true := sr rfl c_S2_10_0
lemma hcheck_S2 : ∀ s ≤ 10, ∀ idx < cnt_S2 s,
    stepExpand (2 ^ (8 * 7) - 1) 7 m1_S2 m2_S2 m4_S2 m8_S2 rs_S2 rf_S2 certHit_S2 s (decSt_S2 s idx) = false := by
  have htop : (2 ^ (8 * 7) - 1) = top_S2 := by decide +kernel
  rw [htop]
  have hfail : ∀ k idx, (∀ i, 0 ≤ i → i < cnt_S2 k → chk_S2 k i = true) → idx < cnt_S2 k →
      stepExpand top_S2 7 m1_S2 m2_S2 m4_S2 m8_S2 rs_S2 rf_S2 certHit_S2 k (decSt_S2 k idx) = false := by
    intro k idx hall hi; have h1 := hall idx (Nat.zero_le _) hi; unfold chk_S2 at h1
    cases hse : stepExpand top_S2 7 m1_S2 m2_S2 m4_S2 m8_S2 rs_S2 rf_S2 certHit_S2 k (decSt_S2 k idx) <;> simp only [hse] at h1
    · rfl
    · contradiction
  intro s hs idx hidx; interval_cases s
  · have h0 : cnt_S2 0 = 0 := rfl; omega
  · have h0 : cnt_S2 1 = 0 := rfl; omega
  · have h0 : cnt_S2 2 = 0 := rfl; omega
  · have h0 : cnt_S2 3 = 0 := rfl; omega
  · have h0 : cnt_S2 4 = 0 := rfl; omega
  · have h0 : cnt_S2 5 = 0 := rfl; omega
  · have h0 : cnt_S2 6 = 0 := rfl; omega
  · exact hfail 7 idx all_S2_7 hidx
  · exact hfail 8 idx all_S2_8 hidx
  · exact hfail 9 idx all_S2_9 hidx
  · exact hfail 10 idx all_S2_10 hidx
lemma r_S2_0 : searchCert top_S2 7 m1_S2 m2_S2 m4_S2 m8_S2 rs_S2 rf_S2 certHit_S2 9 (mkLitWt top_S2 litW_S2 [2, 0, 2, 2, 2, 2, 0] false) = false := by decide +kernel
lemma r_S2_1 : searchCert top_S2 7 m1_S2 m2_S2 m4_S2 m8_S2 rs_S2 rf_S2 certHit_S2 10 (mkLitWt top_S2 litW_S2 [1, 0, 1, 1, 1, 1, 0] false) = false := by decide +kernel
lemma no_S2 : ¬ HasMono pos_S2 neg_S2 (initOf vs_S2 false) 10 := by
  have htop : 2 ^ (pos_S2.length * neg_S2.length) - 1 = top_S2 := by decide +kernel
  have hms : checkMasks pos_S2.length neg_S2.length m1_S2 m2_S2 m4_S2 m8_S2 rs_S2 = true := by decide +kernel
  intro h
  obtain ⟨k1, hk1, hm1⟩ := hasMono_to_monoLive (by decide) (by decide) 10 _ h
  obtain ⟨k2, hk2, U, hUW, hUnd, hSU⟩ := monoLive_to_sMonoLive k1 _ hm1
  obtain ⟨hperm, hlen⟩ := classify_U_noW9 (by decide) (by decide +kernel) hUW hUnd hSU
  have hk_min : 9 ≤ k2 := by
    by_contra hlt
    have hv : varF 1 ∈ U := hperm.mem_iff.2 (by simp [vs_S2])
    have ⟨_, hhm⟩ := one_zero_wire_save_one sub_S2_1.1 k2 U (fun u hu => initOf_mono _ _ u (hUW u hu)) hSU _ hv (by funext x; simp [projV, varF])
    exact sub_S2_1.2 U hUW (hasMono_mono_k (by omega) hhm)
  have hk_le : k2 ≤ 10 := by omega
  have hSub0 : ∀ u ∈ vs_S2.map varF, u ∈ initOf vs_S2 false := fun u hu => by simp [initOf, hu]
  interval_cases k2
  ·
    refine close_ht_case (vs := vs_S2) (tgs := [2, 0, 2, 2, 2, 2, 0]) (withW9 := false) (cap := 10) (by decide) (by decide) (by decide) htop hms (by decide) (by decide) encLit_S2 decSt_S2_ok certHit_S2_sound hcheck_S2 (by omega) ?_ (sMonoLive_perm hperm hSU) r_S2_0
    intro wt hwt; simp only [mkWt, vs_S2, List.zipWith_cons_cons, List.zipWith_nil_left, List.append_nil, List.mem_cons, List.not_mem_nil, or_false, ite_false, Bool.false_eq_true] at hwt; rcases hwt with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact tagOk_of_sub sub_S2_1 hSub0 (Or.inr ⟨rfl, by omega⟩)
    · trivial
    · exact tagOk_of_sub sub_S2_3 hSub0 (Or.inr ⟨rfl, by omega⟩)
    · exact tagOk_of_sub sub_S2_5 hSub0 (Or.inr ⟨rfl, by omega⟩)
    · exact tagOk_of_sub sub_S2_6 hSub0 (Or.inr ⟨rfl, by omega⟩)
    · exact tagOk_of_sub sub_S2_7 hSub0 (Or.inr ⟨rfl, by omega⟩)
    · trivial
  ·
    refine close_ht_case (vs := vs_S2) (tgs := [1, 0, 1, 1, 1, 1, 0]) (withW9 := false) (cap := 10) (by decide) (by decide) (by decide) htop hms (by decide) (by decide) encLit_S2 decSt_S2_ok certHit_S2_sound hcheck_S2 (by omega) ?_ (sMonoLive_perm hperm hSU) r_S2_1
    intro wt hwt; simp only [mkWt, vs_S2, List.zipWith_cons_cons, List.zipWith_nil_left, List.append_nil, List.mem_cons, List.not_mem_nil, or_false, ite_false, Bool.false_eq_true] at hwt; rcases hwt with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact tagOk_of_sub sub_S2_1 hSub0 (Or.inl ⟨rfl, by omega⟩)
    · trivial
    · exact tagOk_of_sub sub_S2_3 hSub0 (Or.inl ⟨rfl, by omega⟩)
    · exact tagOk_of_sub sub_S2_5 hSub0 (Or.inl ⟨rfl, by omega⟩)
    · exact tagOk_of_sub sub_S2_6 hSub0 (Or.inl ⟨rfl, by omega⟩)
    · exact tagOk_of_sub sub_S2_7 hSub0 (Or.inl ⟨rfl, by omega⟩)
    · trivial

-- S1 (V=8, P=9, N=9, w9=0, k=11)
def pos_S1 : List Nat := [6, 12, 24, 66, 132, 160, 264, 288, 320]
def neg_S1 : List Nat := [42, 50, 104, 116, 138, 200, 208, 276, 402]
def vs_S1 : List (Fin 9) := [1, 2, 3, 4, 5, 6, 7, 8]
lemma no_S1 : ¬ HasMono pos_S1 neg_S1 (initOf vs_S1 false) 11 :=
  instant_kill_fast 4 (fun i : Fin 9 => (match i.1 with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8 : Fin 9)) (by decide) (by decide) (by decide +kernel) (by omega)
    (by decide +kernel) (by decide +kernel) (by decide) (by decide) (by decide +kernel) no_S2

-- S7 (V=6, P=6, N=5, w9=1, k=7)
def pos_S7 : List Nat := [3, 17, 33, 66, 288, 320]
def neg_S7 : List Nat := [50, 65, 112, 257, 274]
def vs_S7 : List (Fin 9) := [0, 1, 4, 5, 6, 8]
def top_S7 : Nat := 0x3fffffff
def m1_S7 : Nat := 0x1ef7bdef
def m2_S7 : Nat := 0xe739ce7
def m4_S7 : Nat := 0x2108421
def m8_S7 : Nat := 0
def rs_S7 : Nat := 0x2108421
def rf_S7 : Nat := 31
def litW_S7 : List (Nat × Nat) := [(0x7fff, 0x14a5294a), (0xf801f, 0x2318c631), (0x3e0, 0x2b5ad6b5), (0x1f07c00, 0xa5294a5), (0x3e0f8000, 0xc6318c6), (0x3ff00000, 0x318c6318), (0xfffff, 0x37bdef7b)]
lemma encLit_S7 : (initOf vs_S7 true).map (fun f => (encPos pos_S7 neg_S7.length f, encNeg pos_S7.length neg_S7 f)) = litW_S7 := by decide +kernel
lemma r_S7_0 : searchCert top_S7 5 m1_S7 m2_S7 m4_S7 m8_S7 rs_S7 rf_S7 (fun _ _ => false) 5 (mkLitWt top_S7 litW_S7 [0, 0, 0, 0, 0, 0] false) = false := by decide +kernel
lemma r_S7_1 : searchCert top_S7 5 m1_S7 m2_S7 m4_S7 m8_S7 rs_S7 rf_S7 (fun _ _ => false) 5 (mkLitWt top_S7 litW_S7 [0, 0, 0, 0, 0, 0] true) = false := by decide +kernel
lemma r_S7_2 : searchCert top_S7 5 m1_S7 m2_S7 m4_S7 m8_S7 rs_S7 rf_S7 (fun _ _ => false) 6 (mkLitWt top_S7 litW_S7 [0, 0, 0, 0, 0, 0] false) = false := by decide +kernel
lemma r_S7_3 : searchCert top_S7 5 m1_S7 m2_S7 m4_S7 m8_S7 rs_S7 rf_S7 (fun _ _ => false) 6 (mkLitWt top_S7 litW_S7 [0, 0, 0, 0, 0, 0] true) = false := by decide +kernel
lemma r_S7_4 : searchCert top_S7 5 m1_S7 m2_S7 m4_S7 m8_S7 rs_S7 rf_S7 (fun _ _ => false) 7 (mkLitWt top_S7 litW_S7 [0, 0, 0, 0, 0, 0] false) = false := by decide +kernel
lemma r_S7_5 : searchCert top_S7 5 m1_S7 m2_S7 m4_S7 m8_S7 rs_S7 rf_S7 (fun _ _ => false) 7 (mkLitWt top_S7 litW_S7 [0, 0, 0, 0, 0, 0] true) = false := by decide +kernel
lemma no_S7 : ¬ HasMono pos_S7 neg_S7 (initOf vs_S7 true) 7 := by
  have htop : 2 ^ (pos_S7.length * neg_S7.length) - 1 = top_S7 := by decide +kernel
  have hms : checkMasks pos_S7.length neg_S7.length m1_S7 m2_S7 m4_S7 m8_S7 rs_S7 = true := by decide +kernel
  intro h
  obtain ⟨k1, hk1, hm1⟩ := hasMono_to_monoLive (by decide) (by decide) 7 _ h
  obtain ⟨k2, hk2, U, hUW, hUnd, hSU⟩ := monoLive_to_sMonoLive k1 _ hm1
  obtain ⟨hperm, hlen⟩ := classify_U_w9 (by decide) (by decide +kernel) hUW hUnd hSU
  have hk_min : 5 ≤ k2 := by simp [vs_S7] at hlen; omega
  have hk_le : k2 ≤ 7 := by omega
  interval_cases k2
  · rcases hperm with hperm | hperm
    ·
      exact close_dir_case (vs := vs_S7) (tgs := [0, 0, 0, 0, 0, 0]) (withW9 := false) (by decide) (by decide) (by decide) htop hms (by decide) (by decide) encLit_S7 (tags_zero_ok (by decide)) (sMonoLive_perm hperm hSU) r_S7_0
    ·
      exact close_dir_case (vs := vs_S7) (tgs := [0, 0, 0, 0, 0, 0]) (withW9 := true) (by decide) (by decide) (by decide) htop hms (by decide) (by decide) encLit_S7 (tags_zero_ok (by decide)) (sMonoLive_perm hperm hSU) r_S7_1
  · rcases hperm with hperm | hperm
    ·
      exact close_dir_case (vs := vs_S7) (tgs := [0, 0, 0, 0, 0, 0]) (withW9 := false) (by decide) (by decide) (by decide) htop hms (by decide) (by decide) encLit_S7 (tags_zero_ok (by decide)) (sMonoLive_perm hperm hSU) r_S7_2
    ·
      exact close_dir_case (vs := vs_S7) (tgs := [0, 0, 0, 0, 0, 0]) (withW9 := true) (by decide) (by decide) (by decide) htop hms (by decide) (by decide) encLit_S7 (tags_zero_ok (by decide)) (sMonoLive_perm hperm hSU) r_S7_3
  · rcases hperm with hperm | hperm
    ·
      exact close_dir_case (vs := vs_S7) (tgs := [0, 0, 0, 0, 0, 0]) (withW9 := false) (by decide) (by decide) (by decide) htop hms (by decide) (by decide) encLit_S7 (tags_zero_ok (by decide)) (sMonoLive_perm hperm hSU) r_S7_4
    ·
      exact close_dir_case (vs := vs_S7) (tgs := [0, 0, 0, 0, 0, 0]) (withW9 := true) (by decide) (by decide) (by decide) htop hms (by decide) (by decide) encLit_S7 (tags_zero_ok (by decide)) (sMonoLive_perm hperm hSU) r_S7_5

-- S8 (V=6, P=6, N=5, w9=1, k=7)
def pos_S8 : List Nat := [3, 33, 66, 264, 288, 320]
def neg_S8 : List Nat := [42, 73, 104, 257, 258]
def vs_S8 : List (Fin 9) := [0, 1, 3, 5, 6, 8]
def top_S8 : Nat := 0x3fffffff
def m1_S8 : Nat := 0x1ef7bdef
def m2_S8 : Nat := 0xe739ce7
def m4_S8 : Nat := 0x2108421
def m8_S8 : Nat := 0
def rs_S8 : Nat := 0x2108421
def rf_S8 : Nat := 31
def litW_S8 : List (Nat × Nat) := [(0x3ff, 0x14a5294a), (0x7c1f, 0x2318c631), (0xf8000, 0xe739ce7), (0x1f003e0, 0xa5294a5), (0x3e007c00, 0xc6318c6), (0x3fff8000, 0x318c6318), (0x7fff, 0x37bdef7b)]
lemma encLit_S8 : (initOf vs_S8 true).map (fun f => (encPos pos_S8 neg_S8.length f, encNeg pos_S8.length neg_S8 f)) = litW_S8 := by decide +kernel
lemma r_S8_0 : searchCert top_S8 5 m1_S8 m2_S8 m4_S8 m8_S8 rs_S8 rf_S8 (fun _ _ => false) 5 (mkLitWt top_S8 litW_S8 [0, 0, 0, 0, 0, 0] false) = false := by decide +kernel
lemma r_S8_1 : searchCert top_S8 5 m1_S8 m2_S8 m4_S8 m8_S8 rs_S8 rf_S8 (fun _ _ => false) 5 (mkLitWt top_S8 litW_S8 [0, 0, 0, 0, 0, 0] true) = false := by decide +kernel
lemma r_S8_2 : searchCert top_S8 5 m1_S8 m2_S8 m4_S8 m8_S8 rs_S8 rf_S8 (fun _ _ => false) 6 (mkLitWt top_S8 litW_S8 [0, 0, 0, 0, 0, 0] false) = false := by decide +kernel
lemma r_S8_3 : searchCert top_S8 5 m1_S8 m2_S8 m4_S8 m8_S8 rs_S8 rf_S8 (fun _ _ => false) 6 (mkLitWt top_S8 litW_S8 [0, 0, 0, 0, 0, 0] true) = false := by decide +kernel
lemma r_S8_4 : searchCert top_S8 5 m1_S8 m2_S8 m4_S8 m8_S8 rs_S8 rf_S8 (fun _ _ => false) 7 (mkLitWt top_S8 litW_S8 [0, 0, 0, 0, 0, 0] false) = false := by decide +kernel
lemma r_S8_5 : searchCert top_S8 5 m1_S8 m2_S8 m4_S8 m8_S8 rs_S8 rf_S8 (fun _ _ => false) 7 (mkLitWt top_S8 litW_S8 [0, 0, 0, 0, 0, 0] true) = false := by decide +kernel
lemma no_S8 : ¬ HasMono pos_S8 neg_S8 (initOf vs_S8 true) 7 := by
  have htop : 2 ^ (pos_S8.length * neg_S8.length) - 1 = top_S8 := by decide +kernel
  have hms : checkMasks pos_S8.length neg_S8.length m1_S8 m2_S8 m4_S8 m8_S8 rs_S8 = true := by decide +kernel
  intro h
  obtain ⟨k1, hk1, hm1⟩ := hasMono_to_monoLive (by decide) (by decide) 7 _ h
  obtain ⟨k2, hk2, U, hUW, hUnd, hSU⟩ := monoLive_to_sMonoLive k1 _ hm1
  obtain ⟨hperm, hlen⟩ := classify_U_w9 (by decide) (by decide +kernel) hUW hUnd hSU
  have hk_min : 5 ≤ k2 := by simp [vs_S8] at hlen; omega
  have hk_le : k2 ≤ 7 := by omega
  interval_cases k2
  · rcases hperm with hperm | hperm
    ·
      exact close_dir_case (vs := vs_S8) (tgs := [0, 0, 0, 0, 0, 0]) (withW9 := false) (by decide) (by decide) (by decide) htop hms (by decide) (by decide) encLit_S8 (tags_zero_ok (by decide)) (sMonoLive_perm hperm hSU) r_S8_0
    ·
      exact close_dir_case (vs := vs_S8) (tgs := [0, 0, 0, 0, 0, 0]) (withW9 := true) (by decide) (by decide) (by decide) htop hms (by decide) (by decide) encLit_S8 (tags_zero_ok (by decide)) (sMonoLive_perm hperm hSU) r_S8_1
  · rcases hperm with hperm | hperm
    ·
      exact close_dir_case (vs := vs_S8) (tgs := [0, 0, 0, 0, 0, 0]) (withW9 := false) (by decide) (by decide) (by decide) htop hms (by decide) (by decide) encLit_S8 (tags_zero_ok (by decide)) (sMonoLive_perm hperm hSU) r_S8_2
    ·
      exact close_dir_case (vs := vs_S8) (tgs := [0, 0, 0, 0, 0, 0]) (withW9 := true) (by decide) (by decide) (by decide) htop hms (by decide) (by decide) encLit_S8 (tags_zero_ok (by decide)) (sMonoLive_perm hperm hSU) r_S8_3
  · rcases hperm with hperm | hperm
    ·
      exact close_dir_case (vs := vs_S8) (tgs := [0, 0, 0, 0, 0, 0]) (withW9 := false) (by decide) (by decide) (by decide) htop hms (by decide) (by decide) encLit_S8 (tags_zero_ok (by decide)) (sMonoLive_perm hperm hSU) r_S8_4
    ·
      exact close_dir_case (vs := vs_S8) (tgs := [0, 0, 0, 0, 0, 0]) (withW9 := true) (by decide) (by decide) (by decide) htop hms (by decide) (by decide) encLit_S8 (tags_zero_ok (by decide)) (sMonoLive_perm hperm hSU) r_S8_5

-- S9 (V=6, P=6, N=5, w9=1, k=7)
def pos_S9 : List Nat := [3, 17, 24, 66, 264, 320]
def neg_S9 : List Nat := [10, 73, 80, 257, 274]
def vs_S9 : List (Fin 9) := [0, 1, 3, 4, 6, 8]
def top_S9 : Nat := 0x3fffffff
def m1_S9 : Nat := 0x1ef7bdef
def m2_S9 : Nat := 0xe739ce7
def m4_S9 : Nat := 0x2108421
def m8_S9 : Nat := 0
def rs_S9 : Nat := 0x2108421
def rf_S9 : Nat := 31
def litW_S9 : List (Nat × Nat) := [(0x3ff, 0x14a5294a), (0xf801f, 0x2318c631), (0x1f07c00, 0x6318c63), (0x7fe0, 0x294a5294), (0x3e0f8000, 0xc6318c6), (0x3ff00000, 0x318c6318), (0xf83ff, 0x37bdef7b)]
lemma encLit_S9 : (initOf vs_S9 true).map (fun f => (encPos pos_S9 neg_S9.length f, encNeg pos_S9.length neg_S9 f)) = litW_S9 := by decide +kernel
lemma r_S9_0 : searchCert top_S9 5 m1_S9 m2_S9 m4_S9 m8_S9 rs_S9 rf_S9 (fun _ _ => false) 5 (mkLitWt top_S9 litW_S9 [0, 0, 0, 0, 0, 0] false) = false := by decide +kernel
lemma r_S9_1 : searchCert top_S9 5 m1_S9 m2_S9 m4_S9 m8_S9 rs_S9 rf_S9 (fun _ _ => false) 5 (mkLitWt top_S9 litW_S9 [0, 0, 0, 0, 0, 0] true) = false := by decide +kernel
lemma r_S9_2 : searchCert top_S9 5 m1_S9 m2_S9 m4_S9 m8_S9 rs_S9 rf_S9 (fun _ _ => false) 6 (mkLitWt top_S9 litW_S9 [0, 0, 0, 0, 0, 0] false) = false := by decide +kernel
lemma r_S9_3 : searchCert top_S9 5 m1_S9 m2_S9 m4_S9 m8_S9 rs_S9 rf_S9 (fun _ _ => false) 6 (mkLitWt top_S9 litW_S9 [0, 0, 0, 0, 0, 0] true) = false := by decide +kernel
lemma r_S9_4 : searchCert top_S9 5 m1_S9 m2_S9 m4_S9 m8_S9 rs_S9 rf_S9 (fun _ _ => false) 7 (mkLitWt top_S9 litW_S9 [0, 0, 0, 0, 0, 0] false) = false := by decide +kernel
lemma r_S9_5 : searchCert top_S9 5 m1_S9 m2_S9 m4_S9 m8_S9 rs_S9 rf_S9 (fun _ _ => false) 7 (mkLitWt top_S9 litW_S9 [0, 0, 0, 0, 0, 0] true) = false := by decide +kernel
lemma no_S9 : ¬ HasMono pos_S9 neg_S9 (initOf vs_S9 true) 7 := by
  have htop : 2 ^ (pos_S9.length * neg_S9.length) - 1 = top_S9 := by decide +kernel
  have hms : checkMasks pos_S9.length neg_S9.length m1_S9 m2_S9 m4_S9 m8_S9 rs_S9 = true := by decide +kernel
  intro h
  obtain ⟨k1, hk1, hm1⟩ := hasMono_to_monoLive (by decide) (by decide) 7 _ h
  obtain ⟨k2, hk2, U, hUW, hUnd, hSU⟩ := monoLive_to_sMonoLive k1 _ hm1
  obtain ⟨hperm, hlen⟩ := classify_U_w9 (by decide) (by decide +kernel) hUW hUnd hSU
  have hk_min : 5 ≤ k2 := by simp [vs_S9] at hlen; omega
  have hk_le : k2 ≤ 7 := by omega
  interval_cases k2
  · rcases hperm with hperm | hperm
    ·
      exact close_dir_case (vs := vs_S9) (tgs := [0, 0, 0, 0, 0, 0]) (withW9 := false) (by decide) (by decide) (by decide) htop hms (by decide) (by decide) encLit_S9 (tags_zero_ok (by decide)) (sMonoLive_perm hperm hSU) r_S9_0
    ·
      exact close_dir_case (vs := vs_S9) (tgs := [0, 0, 0, 0, 0, 0]) (withW9 := true) (by decide) (by decide) (by decide) htop hms (by decide) (by decide) encLit_S9 (tags_zero_ok (by decide)) (sMonoLive_perm hperm hSU) r_S9_1
  · rcases hperm with hperm | hperm
    ·
      exact close_dir_case (vs := vs_S9) (tgs := [0, 0, 0, 0, 0, 0]) (withW9 := false) (by decide) (by decide) (by decide) htop hms (by decide) (by decide) encLit_S9 (tags_zero_ok (by decide)) (sMonoLive_perm hperm hSU) r_S9_2
    ·
      exact close_dir_case (vs := vs_S9) (tgs := [0, 0, 0, 0, 0, 0]) (withW9 := true) (by decide) (by decide) (by decide) htop hms (by decide) (by decide) encLit_S9 (tags_zero_ok (by decide)) (sMonoLive_perm hperm hSU) r_S9_3
  · rcases hperm with hperm | hperm
    ·
      exact close_dir_case (vs := vs_S9) (tgs := [0, 0, 0, 0, 0, 0]) (withW9 := false) (by decide) (by decide) (by decide) htop hms (by decide) (by decide) encLit_S9 (tags_zero_ok (by decide)) (sMonoLive_perm hperm hSU) r_S9_4
    ·
      exact close_dir_case (vs := vs_S9) (tgs := [0, 0, 0, 0, 0, 0]) (withW9 := true) (by decide) (by decide) (by decide) htop hms (by decide) (by decide) encLit_S9 (tags_zero_ok (by decide)) (sMonoLive_perm hperm hSU) r_S9_5

-- S10 (V=6, P=6, N=5, w9=1, k=7)
def pos_S10 : List Nat := [3, 17, 24, 33, 264, 288]
def neg_S10 : List Nat := [9, 42, 50, 257, 274]
def vs_S10 : List (Fin 9) := [0, 1, 3, 4, 5, 8]
def top_S10 : Nat := 0x3fffffff
def m1_S10 : Nat := 0x1ef7bdef
def m2_S10 : Nat := 0xe739ce7
def m4_S10 : Nat := 0x2108421
def m8_S10 : Nat := 0
def rs_S10 : Nat := 0x2108421
def rf_S10 : Nat := 31
def litW_S10 : List (Nat × Nat) := [(0xf83ff, 0x1294a529), (0x1f, 0x2d6b5ad6), (0x1f07c00, 0x6318c63), (0x7fe0, 0x294a5294), (0x3e0f8000, 0xc6318c6), (0x3ff00000, 0x318c6318), (0xf83ff, 0x3fffffff)]
lemma encLit_S10 : (initOf vs_S10 true).map (fun f => (encPos pos_S10 neg_S10.length f, encNeg pos_S10.length neg_S10 f)) = litW_S10 := by decide +kernel
lemma r_S10_0 : searchCert top_S10 5 m1_S10 m2_S10 m4_S10 m8_S10 rs_S10 rf_S10 (fun _ _ => false) 5 (mkLitWt top_S10 litW_S10 [0, 0, 0, 0, 0, 0] false) = false := by decide +kernel
lemma r_S10_1 : searchCert top_S10 5 m1_S10 m2_S10 m4_S10 m8_S10 rs_S10 rf_S10 (fun _ _ => false) 5 (mkLitWt top_S10 litW_S10 [0, 0, 0, 0, 0, 0] true) = false := by decide +kernel
lemma r_S10_2 : searchCert top_S10 5 m1_S10 m2_S10 m4_S10 m8_S10 rs_S10 rf_S10 (fun _ _ => false) 6 (mkLitWt top_S10 litW_S10 [0, 0, 0, 0, 0, 0] false) = false := by decide +kernel
lemma r_S10_3 : searchCert top_S10 5 m1_S10 m2_S10 m4_S10 m8_S10 rs_S10 rf_S10 (fun _ _ => false) 6 (mkLitWt top_S10 litW_S10 [0, 0, 0, 0, 0, 0] true) = false := by decide +kernel
lemma r_S10_4 : searchCert top_S10 5 m1_S10 m2_S10 m4_S10 m8_S10 rs_S10 rf_S10 (fun _ _ => false) 7 (mkLitWt top_S10 litW_S10 [0, 0, 0, 0, 0, 0] false) = false := by decide +kernel
lemma r_S10_5 : searchCert top_S10 5 m1_S10 m2_S10 m4_S10 m8_S10 rs_S10 rf_S10 (fun _ _ => false) 7 (mkLitWt top_S10 litW_S10 [0, 0, 0, 0, 0, 0] true) = false := by decide +kernel
lemma no_S10 : ¬ HasMono pos_S10 neg_S10 (initOf vs_S10 true) 7 := by
  have htop : 2 ^ (pos_S10.length * neg_S10.length) - 1 = top_S10 := by decide +kernel
  have hms : checkMasks pos_S10.length neg_S10.length m1_S10 m2_S10 m4_S10 m8_S10 rs_S10 = true := by decide +kernel
  intro h
  obtain ⟨k1, hk1, hm1⟩ := hasMono_to_monoLive (by decide) (by decide) 7 _ h
  obtain ⟨k2, hk2, U, hUW, hUnd, hSU⟩ := monoLive_to_sMonoLive k1 _ hm1
  obtain ⟨hperm, hlen⟩ := classify_U_w9 (by decide) (by decide +kernel) hUW hUnd hSU
  have hk_min : 5 ≤ k2 := by simp [vs_S10] at hlen; omega
  have hk_le : k2 ≤ 7 := by omega
  interval_cases k2
  · rcases hperm with hperm | hperm
    ·
      exact close_dir_case (vs := vs_S10) (tgs := [0, 0, 0, 0, 0, 0]) (withW9 := false) (by decide) (by decide) (by decide) htop hms (by decide) (by decide) encLit_S10 (tags_zero_ok (by decide)) (sMonoLive_perm hperm hSU) r_S10_0
    ·
      exact close_dir_case (vs := vs_S10) (tgs := [0, 0, 0, 0, 0, 0]) (withW9 := true) (by decide) (by decide) (by decide) htop hms (by decide) (by decide) encLit_S10 (tags_zero_ok (by decide)) (sMonoLive_perm hperm hSU) r_S10_1
  · rcases hperm with hperm | hperm
    ·
      exact close_dir_case (vs := vs_S10) (tgs := [0, 0, 0, 0, 0, 0]) (withW9 := false) (by decide) (by decide) (by decide) htop hms (by decide) (by decide) encLit_S10 (tags_zero_ok (by decide)) (sMonoLive_perm hperm hSU) r_S10_2
    ·
      exact close_dir_case (vs := vs_S10) (tgs := [0, 0, 0, 0, 0, 0]) (withW9 := true) (by decide) (by decide) (by decide) htop hms (by decide) (by decide) encLit_S10 (tags_zero_ok (by decide)) (sMonoLive_perm hperm hSU) r_S10_3
  · rcases hperm with hperm | hperm
    ·
      exact close_dir_case (vs := vs_S10) (tgs := [0, 0, 0, 0, 0, 0]) (withW9 := false) (by decide) (by decide) (by decide) htop hms (by decide) (by decide) encLit_S10 (tags_zero_ok (by decide)) (sMonoLive_perm hperm hSU) r_S10_4
    ·
      exact close_dir_case (vs := vs_S10) (tgs := [0, 0, 0, 0, 0, 0]) (withW9 := true) (by decide) (by decide) (by decide) htop hms (by decide) (by decide) encLit_S10 (tags_zero_ok (by decide)) (sMonoLive_perm hperm hSU) r_S10_5

-- S6 (V=7, P=8, N=7, w9=1, k=10)
def pos_S6 : List Nat := [3, 17, 24, 33, 66, 264, 288, 320]
def neg_S6 : List Nat := [42, 50, 73, 104, 112, 257, 274]
def vs_S6 : List (Fin 9) := [0, 1, 3, 4, 5, 6, 8]
def top_S6 : Nat := 0xffffffffffffff
def m1_S6 : Nat := 0x7efdfbf7efdfbf
def m2_S6 : Nat := 0x3e7cf9f3e7cf9f
def m4_S6 : Nat := 0xe1c3870e1c387
def m8_S6 : Nat := 0
def rs_S6 : Nat := 0x2040810204081
def rf_S6 : Nat := 127
def litW_S6 : List (Nat × Nat) := [(0xfe03fff, 0x48912244891224), (0x7f000007f, 0x870e1c3870e1c3), (0x3f8001fc000, 0x1a3468d1a3468d), (0x1fff80, 0xa54a952a54a952), (0x1fc000fe00000, 0x366cd9b366cd9b), (0xfe0007f0000000, 0x3870e1c3870e1c), (0xfffff800000000, 0xc183060c183060), (0x7ffe03fff, 0xcf9f3e7cf9f3e7)]
lemma encLit_S6 : (initOf vs_S6 true).map (fun f => (encPos pos_S6 neg_S6.length f, encNeg pos_S6.length neg_S6 f)) = litW_S6 := by decide +kernel
def pi_S6_1 : Fin 9 → Fin 9 := fun i : Fin 9 => (match i.1 with | 0 => 2 | 1 => 0 | 2 => 1 | 3 => 5 | 4 => 7 | 5 => 3 | 6 => 6 | 7 => 4 | _ => 8 : Fin 9)
lemma sub_S6_1 : SubJust pos_S6 neg_S6 (initOf vs_S6 true) pos_S3 neg_S3 1 pi_S6_1 7 :=
  mkSubJust 1 pi_S6_1 (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) no_S3
def pi_S6_3 : Fin 9 → Fin 9 := fun i : Fin 9 => (match i.1 with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8 : Fin 9)
lemma sub_S6_3 : SubJust pos_S6 neg_S6 (initOf vs_S6 true) pos_S7 neg_S7 3 pi_S6_3 7 :=
  mkSubJust 3 pi_S6_3 (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) no_S7
def pi_S6_4 : Fin 9 → Fin 9 := fun i : Fin 9 => (match i.1 with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8 : Fin 9)
lemma sub_S6_4 : SubJust pos_S6 neg_S6 (initOf vs_S6 true) pos_S8 neg_S8 4 pi_S6_4 7 :=
  mkSubJust 4 pi_S6_4 (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) no_S8
def pi_S6_5 : Fin 9 → Fin 9 := fun i : Fin 9 => (match i.1 with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8 : Fin 9)
lemma sub_S6_5 : SubJust pos_S6 neg_S6 (initOf vs_S6 true) pos_S9 neg_S9 5 pi_S6_5 7 :=
  mkSubJust 5 pi_S6_5 (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) no_S9
def pi_S6_6 : Fin 9 → Fin 9 := fun i : Fin 9 => (match i.1 with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8 : Fin 9)
lemma sub_S6_6 : SubJust pos_S6 neg_S6 (initOf vs_S6 true) pos_S10 neg_S10 6 pi_S6_6 7 :=
  mkSubJust 6 pi_S6_6 (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) no_S10
def wp_S6 (i : Nat) : Nat := (bn (Nat.blt i 2) (bn (Nat.blt i 1) 0xfe0007ffe03ffffffffff000007f0003f80ffffffffffff80fe03fff000007f000007ffe03f800000000000007ffe03fff0000000fe03ffffe0007f000000001fc000fe00000fffff80000000001fc07ffe0007f000000001fff80000007ffe03ffffffc07ffe000000003f8001fc000 0xfffffff01fc07f0003f8001fff80fffff8001fc00001fc000fffff80fffff80fe00000fffffff0000000ffffffffffffffffffffffe03fff00000000003ffffe0007f01fff80000007f000007f000007f01fffff0003f8001fc000fffff8001fff80000007f0003fff000007ffe03fff) (bn (Nat.blt i 3) 0x1fff800000000fe03fff01fc000ffffffffffc000fffc07ffe03ffffffc07ffe0007ffffc07ffffff80fffc000000000001fc000fe03ffffffff80fffffff0000000fe0007f01fc07ffffffffffffffffe0007f0000000fffffff0000000fe03f800003fff01fc07f0003fff01fffff (bn (Nat.blt i 4) 0xfe0007f01ffffffffff80fffff80fe0007f000007ffe0007ffffffffffffffffe03ffffffffffffffffffffffff01ffffffe03fffffffffffe03fff01fc07ffe03fff01fff80fffffff01fc0000003ffffffffff01fff80fffc00001fff80fffffff01ffffffffc07f01fff80fffff80 0xfffffff01fff80000007fffffffffffff80fffffff)))
def wn_S6 (i : Nat) : Nat := (bn (Nat.blt i 2) (bn (Nat.blt i 1) 0x78f1e3c78f1e3cc78f1e3c78f1e35ab56ad5ab56adc993264c993264870e1c3870e1c300000000000000870e1c3870e1c3489122448912243870e1c3870e1c366cd9b366cd9bc183060c183060b76eddbb76eddba54a952a54a952489122448912243e7cf9f3e7cf9f1a3468d1a3468d 0xdfbf7efdfbf7efbf7efdfbf7efdfdbb76eddbb76edb76eddbb76eddbf7efdfbf7efdfbf9f3e7cf9f3e7cefdfbf7efdfbf7cf9f3e7cf9f3e700000000000000bd7af5ebd7af5e00000000000000a74e9d3a74e9d300000000000000e5cb972e5cb972870e1c3870e1c3cf9f3e7cf9f3e7) (bn (Nat.blt i 3) 0x3a74e9d3a74e9d3e7cf9f3e7cf9f7efdfbf7efdfbfbf7efdfbf7efdfbf7efdfbf7efdf000000000000007efdfbf7efdfbfdbb76eddbb76ed00000000000000b76eddbb76eddbf7efdfbf7efdfbeddbb76eddbb76000000000000009f3e7cf9f3e7cfbf7efdfbf7efdf (bn (Nat.blt i 4) 0xbf7efdfbf7efdff7efdfbf7efdfbbf7efdfbf7efdffdfbf7efdfbf7ef9f3e7cf9f3e7cdfbf7efdfbf7efe7cf9f3e7cf9f37af5ebd7af5ebdbf7efdfbf7efdfbf7efdfbf7efdffbf7efdfbf7efddfbf7efdfbf7ef3e7cf9f3e7cf9f7efdfbf7efdfbfbf7efdfbf7efdfbf7efdfbf7efdf 0xfdfbf7efdfbf7eefdfbf7efdfbf7eddbb76eddbb76)))
def st_S6_6 (_ : Nat) : Nat := 0x28100682008016
def htd_S6_6 (_ : Nat) : Nat := 0
def hta_S6_6 (_ : Nat) : Nat := 0x20
def st_S6_7 (_ : Nat) : Nat := 0x501c441007432017180501c2e0e864025c8240c01c2d1e07832018001002858280f032017000501a080f0640256700100285010074324e70012028441007432017001002810068f008017180e01a2e1a07432028180345a200f06404288000501c241007434017
def htd_S6_7 (_ : Nat) : Nat := 0x1002000000040000
def hta_S6_7 (_ : Nat) : Nat := 0x98000000004500000ab360010000002000000007
def st_S6_8 (i : Nat) : Nat := (bn (Nat.blt i 1) 0xa2b01a2e10078340180a2a01c2d10078340180a0345a200f06802a480a0401a2e500803a0180a1c01c2d500803a018180501a2d50074340184e0501a2d100743202820050200d10074340180a0345c200e868029881c050200d10074340180a2501c2e1007434018480501a2e100743401846050e02d10074340180a0385a200e868028880a1401c8410074320281c0501a8410074320280a2001c2e10074320283e0501a2e100743202824050f02d1007432028241d01c2d10074320280a0401a2e100103c0180a1c01c2d100103c018360501a2d100103c0180a0345a3c1001034018340501a2d100103401830050a00e1007432018320501c2d100743201830050200d1007434018200501a3c0f06402568000501a2d040783201720050a00e1e07832018300501a2d1e07832018 (bn (Nat.blt i 2) 0x24050a02e1007432018720501c2e100743201820050200d103303a028680501a2d102e03c198200501a2d1e2e0320280a1601c2d102e032028340501a2d102e0320280a0345ae010078320280a3701a2e10078320280a3601c2d10078320280a0345a200f064042886a0501a2d10078320280a035082e1a0803a1980a1e01c2d1a0803a198460501c2d1a07432028180501a2d1a07432028680501a2e10074320280a0345a34103303a1a83a0501a2d103303a1a80a0401a2e103303a0280a1c01c2d103303a028360501a2d103303a0280a0345a3c102e0320280a0345ac810074340280a3101a2e10074340280a3001c2d10074340280a0345a200e86804bc80a0345a34102e03c1980a035082e102e03c1983a0501a2d102e03c1980a0345a205a078340280a0345ab01007834018 0x840501c2d10078320180a160a02e100783201824050b02d1007832018340e01a2e1007832018820501c2e1007432018300501a2e100743201846050a02e1007432018800501c2d10074320181c051e80d10078320180a3f01c2e100783201824050e02d10074340187c0501c2d1007434018360c01a2d10074340180a3d01a2e1e080320180a1601c2d1e08032018180501a2d1e07832018780501c2d1007832018760501a2d1007832018200501a2e1e07832018740501a2d100743202868050a00e100743202820050200d100103c018200501a2d1e0103401820050200d1e0783401820051280e1007434018180e01a2e1007432018240c01c2d10074320180a0385c200e864025c81c050a00e1007432018))
def htd_S6_8 (_ : Nat) : Nat := 0x400008040200000000000008040001018000000000000000000000002000000002000000001000000000008040000008000400000000000000000000000000000000000000000040000000000200
def hta_S6_8 (i : Nat) : Nat := (bn (Nat.blt i 1) 0x134000000004f000000000023007802c14460000056000385400000007e0800002700000003b00e400000025800000000000285d2010000041e9000168000000000000dab000000045000c0000000054002ca805e02c968e000000100000010800000e8e20863800001100480000000 (bn (Nat.blt i 2) 0x9063100484b5006805700000003c9809100000003a340007c00000000001900000005d24da77eb6aca00000000000000000000000000000002d8f7a0000000dc000000004c2e00000000000601714801000000000192526d0c00a60000000282a80001080000000000000000088000 0x3300028b00001600))
def st_S6_9 (_ : Nat) : Nat := 0x1a014068b4401d0c80a000400a0401a200e86803000200501a2d1e07832018200501a2d1e0803c1900c900280d168d0401d0c80a480142c0385a200f06403240180501a2d1007432019001002850070803a1900c1208014070b4401d0c806400600a0345a200e864030000a0345a206607434028000501a2d1a0803a19014000280d420b8401d0c80a000143c0385a200e864050000a0345a20020783401800050200d170803a1a00c0002870070b4401d0d006000480a0385a200e864030001c0501a2e1007432018000c0280d168803a1900c0002858070b4401e0c806000147a0345c200f064030000a0345a3c1007832018
def htd_S6_9 (_ : Nat) : Nat := 0x81084a0
def hta_S6_9 (_ : Nat) : Nat := 0x44001542c29d6e0100993ec0822976826a00cc0
def st_S6_10 (_ : Nat) : Nat := 0x501a2d1007432017200501a2d1007432018
def htd_S6_10 (_ : Nat) : Nat := 0
def hta_S6_10 (_ : Nat) : Nat := 0x6
def decW_S6 (e : Nat) : W :=
  let s := Nat.shiftRight e 2; let c := Nat.shiftRight s 4; let off := Nat.mul (Nat.land s 15) 56
  let p := Nat.land (Nat.shiftRight (wp_S6 c) off) top_S6; let n := Nat.land (Nat.shiftRight (wn_S6 c) off) top_S6
  ⟨p, n, Nat.land e 3, Nat.land p (Nat.xor n top_S6)⟩
def decWList_S6 : Nat → Nat → List W
  | 0, _ => []
  | n + 1, raw => decW_S6 (Nat.land raw 511) :: decWList_S6 n (Nat.shiftRight raw 9)
lemma decWList_S6_ok : ∀ n raw, WOk top_S6 (decWList_S6 n raw)
  | 0, _ => wOk_nil
  | n + 1, raw => wOk_cons rfl (decWList_S6_ok n _)
def cnt_S6 (k : Nat) : Nat := (bn (Nat.blt k 8) (bn (Nat.blt k 7) (bn (Nat.beq k 6) (1) 0) (bn (Nat.beq k 7) (11) 0)) (bn (Nat.blt k 9) (bn (Nat.beq k 8) (93) 0) (bn (Nat.blt k 10) (bn (Nat.beq k 9) (23) 0) (bn (Nat.beq k 10) (2) 0))))
def decSt_S6 (k idx : Nat) : List W := (match Nat.blt k 8 with | true => (match Nat.blt k 7 with | true => (match Nat.beq k 6 with | true => (stProbe 58 st_S6_6 decWList_S6 idx) | false => []) | false => (match Nat.beq k 7 with | true => (stProbe 76 st_S6_7 decWList_S6 idx) | false => [])) | false => (match Nat.blt k 9 with | true => (match Nat.beq k 8 with | true => (stProbe 76 st_S6_8 decWList_S6 idx) | false => []) | false => (match Nat.blt k 10 with | true => (match Nat.beq k 9 with | true => (stProbe 85 st_S6_9 decWList_S6 idx) | false => []) | false => (match Nat.beq k 10 with | true => (stProbe 76 st_S6_10 decWList_S6 idx) | false => []))))
lemma decSt_S6_ok (s idx : Nat) : WOk (2 ^ (8 * 7) - 1) (decSt_S6 s idx) := by
  have htop : (2 ^ (8 * 7) - 1) = top_S6 := by decide +kernel
  rw [htop]; unfold decSt_S6; repeat (first | apply wOk_match | exact wOk_nil | exact decWList_S6_ok _ _)
def lookup_S6 (k : Nat) (zs : List W) : Nat := (match Nat.blt k 8 with | true => (match Nat.blt k 7 with | true => (match Nat.beq k 6 with | true => (htProbe 1 1 1 9 4 15 1 1 htd_S6_6 hta_S6_6 zs) | false => 0) | false => (match Nat.beq k 7 with | true => (htProbe 1 12 1 50 6 63 4 15 htd_S6_7 hta_S6_7 zs) | false => 0)) | false => (match Nat.blt k 9 with | true => (match Nat.beq k 8 with | true => (htProbe 1 70 3 265 9 511 7 127 htd_S6_8 hta_S6_8 zs) | false => 0) | false => (match Nat.blt k 10 with | true => (match Nat.beq k 9 with | true => (htProbe 1 7 1 31 5 31 5 31 htd_S6_9 hta_S6_9 zs) | false => 0) | false => (match Nat.beq k 10 with | true => (htProbe 1 1 1 5 3 7 2 3 htd_S6_10 hta_S6_10 zs) | false => 0))))
def certHit_S6 (k : Nat) (zs : List W) : Bool :=
  let code := lookup_S6 k zs
  match Nat.beq code 0 with | true => false | false => let q := Nat.sub code 1; match Nat.blt q (cnt_S6 k) with | false => false | true => isPermW zs (decSt_S6 k q)
lemma certHit_S6_sound (s : Nat) (zs : List W)
    (hrc : ∀ w ∈ zs.map W.toPNT, RowColConst 8 7 w.1 w.2.1)
    (hnat : NatTRestricted (2 ^ (8 * 7) - 1) s (zs.map W.toPNT)) (hhit : certHit_S6 s zs = true) :
    ∃ idx < cnt_S6 s, (∀ w ∈ (decSt_S6 s idx).map W.toPNT, RowColConst 8 7 w.1 w.2.1) ∧ NatTRestricted (2 ^ (8 * 7) - 1) s ((decSt_S6 s idx).map W.toPNT) := by
  unfold certHit_S6 at hhit; dsimp only at hhit
  cases h0 : Nat.beq (lookup_S6 s zs) 0 <;> simp only [h0] at hhit
  · cases h1 : Nat.blt (Nat.sub (lookup_S6 s zs) 1) (cnt_S6 s) <;> simp only [h1] at hhit
    · contradiction
    · have hp := isPermW_sound hhit
      exact ⟨_, by simpa [Nat.blt_eq] using h1, fun w hw => hrc w (hp.mem_iff.2 hw), natTRestricted_perm hp hnat⟩
  · contradiction
def chk_S6 (k idx : Nat) : Bool :=
  match stepExpand top_S6 7 m1_S6 m2_S6 m4_S6 m8_S6 rs_S6 rf_S6 certHit_S6 k (decSt_S6 k idx) with | true => false | false => true
lemma c_S6_6_0 : span (chk_S6 6) 1 0 = true := by decide +kernel
lemma all_S6_6 : ∀ i, 0 ≤ i → i < 1 → chk_S6 6 i = true := sr rfl c_S6_6_0
lemma c_S6_7_0 : span (chk_S6 7) 11 0 = true := by decide +kernel
lemma all_S6_7 : ∀ i, 0 ≤ i → i < 11 → chk_S6 7 i = true := sr rfl c_S6_7_0
lemma c_S6_8_0 : span (chk_S6 8) 8 0 = true := by decide +kernel
lemma c_S6_8_1 : span (chk_S6 8) 8 8 = true := by decide +kernel
lemma c_S6_8_2 : span (chk_S6 8) 8 16 = true := by decide +kernel
lemma c_S6_8_3 : span (chk_S6 8) 8 24 = true := by decide +kernel
lemma c_S6_8_4 : span (chk_S6 8) 8 32 = true := by decide +kernel
lemma c_S6_8_5 : span (chk_S6 8) 8 40 = true := by decide +kernel
lemma c_S6_8_6 : span (chk_S6 8) 8 48 = true := by decide +kernel
lemma c_S6_8_7 : span (chk_S6 8) 8 56 = true := by decide +kernel
lemma c_S6_8_8 : span (chk_S6 8) 8 64 = true := by decide +kernel
lemma c_S6_8_9 : span (chk_S6 8) 8 72 = true := by decide +kernel
lemma c_S6_8_10 : span (chk_S6 8) 8 80 = true := by decide +kernel
lemma c_S6_8_11 : span (chk_S6 8) 5 88 = true := by decide +kernel
lemma all_S6_8 : ∀ i, 0 ≤ i → i < 93 → chk_S6 8 i = true := rj (rj (rj (rj (rj (rj (rj (rj (rj (rj (rj (sr rfl c_S6_8_0) (sr rfl c_S6_8_1)) (sr rfl c_S6_8_2)) (sr rfl c_S6_8_3)) (sr rfl c_S6_8_4)) (sr rfl c_S6_8_5)) (sr rfl c_S6_8_6)) (sr rfl c_S6_8_7)) (sr rfl c_S6_8_8)) (sr rfl c_S6_8_9)) (sr rfl c_S6_8_10)) (sr rfl c_S6_8_11)
lemma c_S6_9_0 : span (chk_S6 9) 8 0 = true := by decide +kernel
lemma c_S6_9_1 : span (chk_S6 9) 8 8 = true := by decide +kernel
lemma c_S6_9_2 : span (chk_S6 9) 7 16 = true := by decide +kernel
lemma all_S6_9 : ∀ i, 0 ≤ i → i < 23 → chk_S6 9 i = true := rj (rj (sr rfl c_S6_9_0) (sr rfl c_S6_9_1)) (sr rfl c_S6_9_2)
lemma c_S6_10_0 : span (chk_S6 10) 2 0 = true := by decide +kernel
lemma all_S6_10 : ∀ i, 0 ≤ i → i < 2 → chk_S6 10 i = true := sr rfl c_S6_10_0
lemma hcheck_S6 : ∀ s ≤ 10, ∀ idx < cnt_S6 s,
    stepExpand (2 ^ (8 * 7) - 1) 7 m1_S6 m2_S6 m4_S6 m8_S6 rs_S6 rf_S6 certHit_S6 s (decSt_S6 s idx) = false := by
  have htop : (2 ^ (8 * 7) - 1) = top_S6 := by decide +kernel
  rw [htop]
  have hfail : ∀ k idx, (∀ i, 0 ≤ i → i < cnt_S6 k → chk_S6 k i = true) → idx < cnt_S6 k →
      stepExpand top_S6 7 m1_S6 m2_S6 m4_S6 m8_S6 rs_S6 rf_S6 certHit_S6 k (decSt_S6 k idx) = false := by
    intro k idx hall hi; have h1 := hall idx (Nat.zero_le _) hi; unfold chk_S6 at h1
    cases hse : stepExpand top_S6 7 m1_S6 m2_S6 m4_S6 m8_S6 rs_S6 rf_S6 certHit_S6 k (decSt_S6 k idx) <;> simp only [hse] at h1
    · rfl
    · contradiction
  intro s hs idx hidx; interval_cases s
  · have h0 : cnt_S6 0 = 0 := rfl; omega
  · have h0 : cnt_S6 1 = 0 := rfl; omega
  · have h0 : cnt_S6 2 = 0 := rfl; omega
  · have h0 : cnt_S6 3 = 0 := rfl; omega
  · have h0 : cnt_S6 4 = 0 := rfl; omega
  · have h0 : cnt_S6 5 = 0 := rfl; omega
  · exact hfail 6 idx all_S6_6 hidx
  · exact hfail 7 idx all_S6_7 hidx
  · exact hfail 8 idx all_S6_8 hidx
  · exact hfail 9 idx all_S6_9 hidx
  · exact hfail 10 idx all_S6_10 hidx
lemma r_S6_0 : searchCert top_S6 7 m1_S6 m2_S6 m4_S6 m8_S6 rs_S6 rf_S6 certHit_S6 9 (mkLitWt top_S6 litW_S6 [0, 2, 2, 2, 2, 2, 0] false) = false := by decide +kernel
lemma r_S6_1 : searchCert top_S6 7 m1_S6 m2_S6 m4_S6 m8_S6 rs_S6 rf_S6 certHit_S6 9 (mkLitWt top_S6 litW_S6 [0, 2, 2, 2, 2, 2, 0] true) = false := by decide +kernel
lemma r_S6_2 : searchCert top_S6 7 m1_S6 m2_S6 m4_S6 m8_S6 rs_S6 rf_S6 certHit_S6 10 (mkLitWt top_S6 litW_S6 [0, 1, 1, 1, 1, 1, 0] false) = false := by decide +kernel
lemma r_S6_3 : searchCert top_S6 7 m1_S6 m2_S6 m4_S6 m8_S6 rs_S6 rf_S6 certHit_S6 10 (mkLitWt top_S6 litW_S6 [0, 1, 1, 1, 1, 1, 0] true) = false := by decide +kernel
lemma no_S6 : ¬ HasMono pos_S6 neg_S6 (initOf vs_S6 true) 10 := by
  have htop : 2 ^ (pos_S6.length * neg_S6.length) - 1 = top_S6 := by decide +kernel
  have hms : checkMasks pos_S6.length neg_S6.length m1_S6 m2_S6 m4_S6 m8_S6 rs_S6 = true := by decide +kernel
  intro h
  obtain ⟨k1, hk1, hm1⟩ := hasMono_to_monoLive (by decide) (by decide) 10 _ h
  obtain ⟨k2, hk2, U, hUW, hUnd, hSU⟩ := monoLive_to_sMonoLive k1 _ hm1
  obtain ⟨hperm, hlen⟩ := classify_U_w9 (by decide) (by decide +kernel) hUW hUnd hSU
  have hk_min : 9 ≤ k2 := by
    by_contra hlt
    have hv : varF 1 ∈ U := by rcases hperm with hp | hp <;> exact hp.mem_iff.2 (by simp [vs_S6])
    have ⟨_, hhm⟩ := one_zero_wire_save_one sub_S6_1.1 k2 U (fun u hu => initOf_mono _ _ u (hUW u hu)) hSU _ hv (by funext x; simp [projV, varF])
    exact sub_S6_1.2 U hUW (hasMono_mono_k (by omega) hhm)
  have hk_le : k2 ≤ 10 := by omega
  have hSub0 : ∀ u ∈ vs_S6.map varF, u ∈ initOf vs_S6 true := fun u hu => by simp [initOf, hu]
  interval_cases k2
  · rcases hperm with hperm | hperm
    ·
      refine close_ht_case (vs := vs_S6) (tgs := [0, 2, 2, 2, 2, 2, 0]) (withW9 := false) (cap := 10) (by decide) (by decide) (by decide) htop hms (by decide) (by decide) encLit_S6 decSt_S6_ok certHit_S6_sound hcheck_S6 (by omega) ?_ (sMonoLive_perm hperm hSU) r_S6_0
      intro wt hwt; simp only [mkWt, vs_S6, List.zipWith_cons_cons, List.zipWith_nil_left, List.append_nil, List.mem_cons, List.not_mem_nil, or_false, ite_false, Bool.false_eq_true] at hwt; rcases hwt with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · trivial
      · exact tagOk_of_sub sub_S6_1 hSub0 (Or.inr ⟨rfl, by omega⟩)
      · exact tagOk_of_sub sub_S6_3 hSub0 (Or.inr ⟨rfl, by omega⟩)
      · exact tagOk_of_sub sub_S6_4 hSub0 (Or.inr ⟨rfl, by omega⟩)
      · exact tagOk_of_sub sub_S6_5 hSub0 (Or.inr ⟨rfl, by omega⟩)
      · exact tagOk_of_sub sub_S6_6 hSub0 (Or.inr ⟨rfl, by omega⟩)
      · trivial
    ·
      refine close_ht_case (vs := vs_S6) (tgs := [0, 2, 2, 2, 2, 2, 0]) (withW9 := true) (cap := 10) (by decide) (by decide) (by decide) htop hms (by decide) (by decide) encLit_S6 decSt_S6_ok certHit_S6_sound hcheck_S6 (by omega) ?_ (sMonoLive_perm hperm hSU) r_S6_1
      intro wt hwt; simp only [mkWt, vs_S6, List.zipWith_cons_cons, List.zipWith_nil_left, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false, ite_true] at hwt; rcases hwt with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · trivial
      · exact tagOk_of_sub sub_S6_1 (fun _ h => h) (Or.inr ⟨rfl, by omega⟩)
      · exact tagOk_of_sub sub_S6_3 (fun _ h => h) (Or.inr ⟨rfl, by omega⟩)
      · exact tagOk_of_sub sub_S6_4 (fun _ h => h) (Or.inr ⟨rfl, by omega⟩)
      · exact tagOk_of_sub sub_S6_5 (fun _ h => h) (Or.inr ⟨rfl, by omega⟩)
      · exact tagOk_of_sub sub_S6_6 (fun _ h => h) (Or.inr ⟨rfl, by omega⟩)
      · trivial
      · trivial
  · rcases hperm with hperm | hperm
    ·
      refine close_ht_case (vs := vs_S6) (tgs := [0, 1, 1, 1, 1, 1, 0]) (withW9 := false) (cap := 10) (by decide) (by decide) (by decide) htop hms (by decide) (by decide) encLit_S6 decSt_S6_ok certHit_S6_sound hcheck_S6 (by omega) ?_ (sMonoLive_perm hperm hSU) r_S6_2
      intro wt hwt; simp only [mkWt, vs_S6, List.zipWith_cons_cons, List.zipWith_nil_left, List.append_nil, List.mem_cons, List.not_mem_nil, or_false, ite_false, Bool.false_eq_true] at hwt; rcases hwt with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · trivial
      · exact tagOk_of_sub sub_S6_1 hSub0 (Or.inl ⟨rfl, by omega⟩)
      · exact tagOk_of_sub sub_S6_3 hSub0 (Or.inl ⟨rfl, by omega⟩)
      · exact tagOk_of_sub sub_S6_4 hSub0 (Or.inl ⟨rfl, by omega⟩)
      · exact tagOk_of_sub sub_S6_5 hSub0 (Or.inl ⟨rfl, by omega⟩)
      · exact tagOk_of_sub sub_S6_6 hSub0 (Or.inl ⟨rfl, by omega⟩)
      · trivial
    ·
      refine close_ht_case (vs := vs_S6) (tgs := [0, 1, 1, 1, 1, 1, 0]) (withW9 := true) (cap := 10) (by decide) (by decide) (by decide) htop hms (by decide) (by decide) encLit_S6 decSt_S6_ok certHit_S6_sound hcheck_S6 (by omega) ?_ (sMonoLive_perm hperm hSU) r_S6_3
      intro wt hwt; simp only [mkWt, vs_S6, List.zipWith_cons_cons, List.zipWith_nil_left, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false, ite_true] at hwt; rcases hwt with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · trivial
      · exact tagOk_of_sub sub_S6_1 (fun _ h => h) (Or.inl ⟨rfl, by omega⟩)
      · exact tagOk_of_sub sub_S6_3 (fun _ h => h) (Or.inl ⟨rfl, by omega⟩)
      · exact tagOk_of_sub sub_S6_4 (fun _ h => h) (Or.inl ⟨rfl, by omega⟩)
      · exact tagOk_of_sub sub_S6_5 (fun _ h => h) (Or.inl ⟨rfl, by omega⟩)
      · exact tagOk_of_sub sub_S6_6 (fun _ h => h) (Or.inl ⟨rfl, by omega⟩)
      · trivial
      · trivial

-- S5 (V=8, P=9, N=9, w9=1, k=11)
def pos_S5 : List Nat := [3, 17, 24, 33, 66, 160, 264, 288, 320]
def neg_S5 : List Nat := [42, 50, 104, 112, 138, 201, 208, 385, 402]
def vs_S5 : List (Fin 9) := [0, 1, 3, 4, 5, 6, 7, 8]
lemma no_S5 : ¬ HasMono pos_S5 neg_S5 (initOf vs_S5 true) 11 :=
  instant_kill_fast 7 (fun i : Fin 9 => (match i.1 with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8 : Fin 9)) (by decide) (by decide) (by decide +kernel) (by omega)
    (by decide +kernel) (by decide +kernel) (by decide) (by decide) (by decide +kernel) no_S6

-- S13 (V=6, P=6, N=5, w9=1, k=7)
def pos_S13 : List Nat := [3, 33, 66, 160, 288, 320]
def neg_S13 : List Nat := [34, 96, 193, 385, 386]
def vs_S13 : List (Fin 9) := [0, 1, 5, 6, 7, 8]
def top_S13 : Nat := 0x3fffffff
def m1_S13 : Nat := 0x1ef7bdef
def m2_S13 : Nat := 0xe739ce7
def m4_S13 : Nat := 0x2108421
def m8_S13 : Nat := 0
def rs_S13 : Nat := 0x2108421
def rf_S13 : Nat := 31
def litW_S13 : List (Nat × Nat) := [(0x3ff, 0x18c6318c), (0x7c1f, 0x2318c631), (0x1ff83e0, 0x6318c63), (0x3e007c00, 0xc6318c6), (0xf8000, 0x39ce739c), (0x3ff00000, 0x318c6318), (0x7fff, 0x3bdef7bd)]
lemma encLit_S13 : (initOf vs_S13 true).map (fun f => (encPos pos_S13 neg_S13.length f, encNeg pos_S13.length neg_S13 f)) = litW_S13 := by decide +kernel
lemma r_S13_0 : searchCert top_S13 5 m1_S13 m2_S13 m4_S13 m8_S13 rs_S13 rf_S13 (fun _ _ => false) 5 (mkLitWt top_S13 litW_S13 [0, 0, 0, 0, 0, 0] false) = false := by decide +kernel
lemma r_S13_1 : searchCert top_S13 5 m1_S13 m2_S13 m4_S13 m8_S13 rs_S13 rf_S13 (fun _ _ => false) 5 (mkLitWt top_S13 litW_S13 [0, 0, 0, 0, 0, 0] true) = false := by decide +kernel
lemma r_S13_2 : searchCert top_S13 5 m1_S13 m2_S13 m4_S13 m8_S13 rs_S13 rf_S13 (fun _ _ => false) 6 (mkLitWt top_S13 litW_S13 [0, 0, 0, 0, 0, 0] false) = false := by decide +kernel
lemma r_S13_3 : searchCert top_S13 5 m1_S13 m2_S13 m4_S13 m8_S13 rs_S13 rf_S13 (fun _ _ => false) 6 (mkLitWt top_S13 litW_S13 [0, 0, 0, 0, 0, 0] true) = false := by decide +kernel
lemma r_S13_4 : searchCert top_S13 5 m1_S13 m2_S13 m4_S13 m8_S13 rs_S13 rf_S13 (fun _ _ => false) 7 (mkLitWt top_S13 litW_S13 [0, 0, 0, 0, 0, 0] false) = false := by decide +kernel
lemma r_S13_5 : searchCert top_S13 5 m1_S13 m2_S13 m4_S13 m8_S13 rs_S13 rf_S13 (fun _ _ => false) 7 (mkLitWt top_S13 litW_S13 [0, 0, 0, 0, 0, 0] true) = false := by decide +kernel
lemma no_S13 : ¬ HasMono pos_S13 neg_S13 (initOf vs_S13 true) 7 := by
  have htop : 2 ^ (pos_S13.length * neg_S13.length) - 1 = top_S13 := by decide +kernel
  have hms : checkMasks pos_S13.length neg_S13.length m1_S13 m2_S13 m4_S13 m8_S13 rs_S13 = true := by decide +kernel
  intro h
  obtain ⟨k1, hk1, hm1⟩ := hasMono_to_monoLive (by decide) (by decide) 7 _ h
  obtain ⟨k2, hk2, U, hUW, hUnd, hSU⟩ := monoLive_to_sMonoLive k1 _ hm1
  obtain ⟨hperm, hlen⟩ := classify_U_w9 (by decide) (by decide +kernel) hUW hUnd hSU
  have hk_min : 5 ≤ k2 := by simp [vs_S13] at hlen; omega
  have hk_le : k2 ≤ 7 := by omega
  interval_cases k2
  · rcases hperm with hperm | hperm
    ·
      exact close_dir_case (vs := vs_S13) (tgs := [0, 0, 0, 0, 0, 0]) (withW9 := false) (by decide) (by decide) (by decide) htop hms (by decide) (by decide) encLit_S13 (tags_zero_ok (by decide)) (sMonoLive_perm hperm hSU) r_S13_0
    ·
      exact close_dir_case (vs := vs_S13) (tgs := [0, 0, 0, 0, 0, 0]) (withW9 := true) (by decide) (by decide) (by decide) htop hms (by decide) (by decide) encLit_S13 (tags_zero_ok (by decide)) (sMonoLive_perm hperm hSU) r_S13_1
  · rcases hperm with hperm | hperm
    ·
      exact close_dir_case (vs := vs_S13) (tgs := [0, 0, 0, 0, 0, 0]) (withW9 := false) (by decide) (by decide) (by decide) htop hms (by decide) (by decide) encLit_S13 (tags_zero_ok (by decide)) (sMonoLive_perm hperm hSU) r_S13_2
    ·
      exact close_dir_case (vs := vs_S13) (tgs := [0, 0, 0, 0, 0, 0]) (withW9 := true) (by decide) (by decide) (by decide) htop hms (by decide) (by decide) encLit_S13 (tags_zero_ok (by decide)) (sMonoLive_perm hperm hSU) r_S13_3
  · rcases hperm with hperm | hperm
    ·
      exact close_dir_case (vs := vs_S13) (tgs := [0, 0, 0, 0, 0, 0]) (withW9 := false) (by decide) (by decide) (by decide) htop hms (by decide) (by decide) encLit_S13 (tags_zero_ok (by decide)) (sMonoLive_perm hperm hSU) r_S13_4
    ·
      exact close_dir_case (vs := vs_S13) (tgs := [0, 0, 0, 0, 0, 0]) (withW9 := true) (by decide) (by decide) (by decide) htop hms (by decide) (by decide) encLit_S13 (tags_zero_ok (by decide)) (sMonoLive_perm hperm hSU) r_S13_5

-- S12 (V=7, P=8, N=7, w9=1, k=10)
def pos_S12 : List Nat := [3, 6, 33, 66, 132, 160, 288, 320]
def neg_S12 : List Nat := [34, 69, 100, 193, 261, 385, 386]
def vs_S12 : List (Fin 9) := [0, 1, 2, 5, 6, 7, 8]
def top_S12 : Nat := 0xffffffffffffff
def m1_S12 : Nat := 0x7efdfbf7efdfbf
def m2_S12 : Nat := 0x3e7cf9f3e7cf9f
def m4_S12 : Nat := 0xe1c3870e1c387
def m8_S12 : Nat := 0
def rs_S12 : Nat := 0x2040810204081
def rf_S12 : Nat := 127
def litW_S12 : List (Nat × Nat) := [(0x1fc07f, 0x74e9d3a74e9d3a), (0xfe03fff, 0x83060c183060c1), (0x7f0003f80, 0x2c58b162c58b16), (0x1fff8001fc000, 0xa142850a14285), (0xfe00000fe00000, 0x1c3870e1c3870e), (0x3fff0000000, 0xd1a3468d1a3468), (0xfffc0000000000, 0xe1c3870e1c3870), (0xfffffff, 0xf7efdfbf7efdfb)]
lemma encLit_S12 : (initOf vs_S12 true).map (fun f => (encPos pos_S12 neg_S12.length f, encNeg pos_S12.length neg_S12 f)) = litW_S12 := by decide +kernel
def pi_S12_0 : Fin 9 → Fin 9 := fun i : Fin 9 => (match i.1 with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8 : Fin 9)
lemma sub_S12_0 : SubJust pos_S12 neg_S12 (initOf vs_S12 true) pos_S4 neg_S4 0 pi_S12_0 7 :=
  mkSubJust 0 pi_S12_0 (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) no_S4
def pi_S12_2 : Fin 9 → Fin 9 := fun i : Fin 9 => (match i.1 with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8 : Fin 9)
lemma sub_S12_2 : SubJust pos_S12 neg_S12 (initOf vs_S12 true) pos_S13 neg_S13 2 pi_S12_2 7 :=
  mkSubJust 2 pi_S12_2 (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) no_S13
def pi_S12_6 : Fin 9 → Fin 9 := fun i : Fin 9 => (match i.1 with | 0 => 0 | 1 => 1 | 2 => 6 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 4 | 7 => 8 | _ => 7 : Fin 9)
lemma sub_S12_6 : SubJust pos_S12 neg_S12 (initOf vs_S12 true) pos_S13 neg_S13 6 pi_S12_6 7 :=
  mkSubJust 6 pi_S12_6 (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) no_S13
def pi_S12_7 : Fin 9 → Fin 9 := fun i : Fin 9 => (match i.1 with | 0 => 1 | 1 => 0 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8 : Fin 9)
lemma sub_S12_7 : SubJust pos_S12 neg_S12 (initOf vs_S12 true) pos_S7 neg_S7 7 pi_S12_7 7 :=
  mkSubJust 7 pi_S12_7 (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) no_S7
def pi_S12_8 : Fin 9 → Fin 9 := fun i : Fin 9 => (match i.1 with | 0 => 1 | 1 => 0 | 2 => 5 | 3 => 2 | 4 => 3 | 5 => 6 | 6 => 4 | 7 => 8 | _ => 7 : Fin 9)
lemma sub_S12_8 : SubJust pos_S12 neg_S12 (initOf vs_S12 true) pos_S7 neg_S7 8 pi_S12_8 7 :=
  mkSubJust 8 pi_S12_8 (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) no_S7
def wp_S12 (i : Nat) : Nat := (bn (Nat.blt i 2) (bn (Nat.blt i 1) 0xfffc000fe03fff01fffff01fff80000007ffe03f80fffff8000000000000000fe03fff000000001fc07f01fff80000000001fff80fffffff0000000fffffff000007f0003f80fffc00000000000003fff00000000000000fffffff000007f01ffffffe00000fe0000001fff8001fc000 0x1fff8001fc07ffffff80ffffffffffc07f0003f80fe0007ffe03f80fffc00001fc07ffffff8001fc000ffffffffffffff0003fffffffffffffc000fffffff000000001fc000000000001fc07ffe0007ffffffff000000001fffff0003fff00000000000000fffffff000007f01fffff) (bn (Nat.blt i 3) 0x3fff01fffff00000000003fff0003fff01fc07fffffffffe03ffffffffff01fc07f0003f8001fc000fffffff01fff8001ffffffffffff01fffff01fffff0003fff0003f80ffffffffffff8001fffff01fc000fffc07ffe03f800000000fe03f80000007ffe03ffffffffff0000000 0xfffffff0003f80fffc07ffe03fff0003ffffe03ffffffc07f01fffff))
def wn_S12 (i : Nat) : Nat := (bn (Nat.blt i 2) (bn (Nat.blt i 1) 0xe3c78f1e3c78f12e5cb972e5cb972c58b162c58b16e1c3870e1c387083060c183060c174e9d3a74e9d3a000000000000008b162c58b162c574e9d3a74e9d3a2c58b162c58b16e1c3870e1c3870d1a3468d1a346883060c183060c12c58b162c58b161c3870e1c3870e0a142850a14285 0x7efdfbf7efdfbfebd7af5ebd7af5eddbb76eddbb763c78f1e3c78f1ef5ebd7af5ebd7aebd7af5ebd7af5f7efdfbf7efdfbf7efdfbf7efdfbf7efdfbf7efdfb02040810204081000000000000007cf9f3e7cf9f3e74e9d3a74e9d3a00000000000000f7efdfbf7efdfb7cf9f3e7cf9f3e) (bn (Nat.blt i 3) 0xfdfbf7efdfbf7e00000000000000f5ebd7af5ebd7af3e7cf9f3e7cf9f5ebd7af5ebd7a00000000000000efdfbf7efdfbf7af5ebd7af5ebd77efdfbf7efdfbffdfbf7efdfbf7e3e7cf9f3e7cf9fdbb76eddbb76edfdfbf7efdfbf7e00000000000000af5ebd7af5ebd7f1e3c78f1e3c78 0xfdfbf7efdfbf7eefdfbf7efdfbf7d3a74e9d3a74e9fdfbf7efdfbf7e))
def fixP_S12_1 : Nat := 0x1fc07f
def swP_S12_1 : List (Nat × Nat) := [(0x3f800000000, 7), (0x3f80, 14), (0x7f0000000, 21)]
def fixN_S12_1 : Nat := 0xcf9f3e7cf9f3e7
def swN_S12_1 : List (Nat × Nat) := [(0x10204081020408, 1)]
def st_S12_6 (_ : Nat) : Nat := 0x1511201c1a060070015110c0805006
def htd_S12_6 (_ : Nat) : Nat := 0
def hta_S12_6 (_ : Nat) : Nat := 0x1000302
def st_S12_7 (_ : Nat) : Nat := 0x15110c1905005670015110c401a0500744151120501a060080015112c4c38050070044152c4005004a7004415112040380573c16112029381a0580015112c1c1a060070015112c2934060070030122c2919050071612202c291905248
def htd_S12_7 (_ : Nat) : Nat := 0
def hta_S12_7 (_ : Nat) : Nat := 0x26000120280c0682a000000000000000000000381600028000064002200002f00000
def st_S12_8 (i : Nat) : Nat := (bn (Nat.blt i 1) 0x15122c2a190500a880016122c29190500248001511202c7c2a1905800a416112c291a05008001511a02c291a050080015112c9c2a1a05008009815122c2938050080015112c402a38050080015112c29941a060080015112c29703806008001590122c29381a058001511202c29381a058007416112c293805008008c16112c291a060080015112c291a06008880015112c502a1a06008007416112c297006008001511842c297006008008068122c291905008006c16112c7c1905008007816112c291905008003c16112029190500800441511202a1905008741611202c291a050091511202c29701a06009006c68112c2a1905008006416122c291905008005c16112c401a05008006015122c401a05008005c1611202919050080015110c2c2919050080015112c401a0500588 0x5c16112c2a1905008009815c42c291a0500800cc16122c291a05008008074122c291a0500800743c112c291a0500800c816112c291a050080015c41284291a0500800c016112c2a1a0500800bc15122c2a1a050080015112c2a1a0500b88006c16112c401a0500800b415122c401a05008001511842c402a050080044151120401a050084415112029701a06009004415112029381a058004415112c401a0500800b016122c29190500800803c122c29190500800ac16122c2a1905008006c3c112c2a1905008)
def htd_S12_8 (_ : Nat) : Nat := 0x10000010205000100020200000005020000010000000300020001000300000002070901000000000000
def hta_S12_8 (i : Nat) : Nat := (bn (Nat.blt i 1) 0xb202bacd4800080000000000000000c6536000002d00000004e0001c0002ecc125c0002c0000000a57c9ca009158c60000000348000017000002f00017c1800144f54000109d01901680c00cc3349a3e61a00000014004d0000061aaab1a36ade9ab00000e7000209b00e2d809e01c8b 0xb400000000003b0acc0000000f93010228096000000e0000000000001e01e800001291)
def st_S12_9 (_ : Nat) : Nat := 0x44151120291905008441511202c291905009446816112c2919050090015112c291905005884415112c29701a06009004415112c401a050084415112c402a1a05009441511842c291a05009984415122c291a05009443c16112c291905009005c16112c2919050085c4416112c291905009447416112c291a05009004416122c2a1a060080015112c29381a05008001511202c291905008006816112c2919050080015112c402a1a05008001511842c291a05008007416112c291a05008009815122c291a05008006c16112c2a1905008003c16112c2919050084415112c29381a05009
def htd_S12_9 (_ : Nat) : Nat := 0x55041040007000000001
def hta_S12_9 (_ : Nat) : Nat := 0x2472fb0e6404296e294014c06d0064d17638000cd21ead53c47c20001d40005c00262408589c02ca01a
def st_S12_10 (_ : Nat) : Nat := 0x15112c2919050074415112c291905008
def htd_S12_10 (_ : Nat) : Nat := 0
def hta_S12_10 (_ : Nat) : Nat := 0x301
def decW_S12 (e : Nat) : W :=
  let s := Nat.shiftRight e 2; let c := Nat.shiftRight s 4; let off := Nat.mul (Nat.land s 15) 56
  let p := Nat.land (Nat.shiftRight (wp_S12 c) off) top_S12; let n := Nat.land (Nat.shiftRight (wn_S12 c) off) top_S12
  ⟨p, n, Nat.land e 3, Nat.land p (Nat.xor n top_S12)⟩
def decWList_S12 : Nat → Nat → List W
  | 0, _ => []
  | n + 1, raw => decW_S12 (Nat.land raw 255) :: decWList_S12 n (Nat.shiftRight raw 8)
lemma decWList_S12_ok : ∀ n raw, WOk top_S12 (decWList_S12 n raw)
  | 0, _ => wOk_nil
  | n + 1, raw => wOk_cons rfl (decWList_S12_ok n _)
def cnt_S12 (k : Nat) : Nat := (bn (Nat.blt k 8) (bn (Nat.blt k 7) (bn (Nat.beq k 6) (2) 0) (bn (Nat.beq k 7) (11) 0)) (bn (Nat.blt k 9) (bn (Nat.beq k 8) (53) 0) (bn (Nat.blt k 10) (bn (Nat.beq k 9) (24) 0) (bn (Nat.beq k 10) (2) 0))))
def decSt_S12 (k idx : Nat) : List W := (match Nat.blt k 8 with | true => (match Nat.blt k 7 with | true => (match Nat.beq k 6 with | true => (stProbe 60 st_S12_6 decWList_S12 idx) | false => []) | false => (match Nat.beq k 7 with | true => (stProbe 68 st_S12_7 decWList_S12 idx) | false => [])) | false => (match Nat.blt k 9 with | true => (match Nat.beq k 8 with | true => (stProbe 76 st_S12_8 decWList_S12 idx) | false => []) | false => (match Nat.blt k 10 with | true => (match Nat.beq k 9 with | true => (stProbe 76 st_S12_9 decWList_S12 idx) | false => []) | false => (match Nat.beq k 10 with | true => (stProbe 68 st_S12_10 decWList_S12 idx) | false => []))))
lemma decSt_S12_ok (s idx : Nat) : WOk (2 ^ (8 * 7) - 1) (decSt_S12 s idx) := by
  have htop : (2 ^ (8 * 7) - 1) = top_S12 := by decide +kernel
  rw [htop]; unfold decSt_S12; repeat (first | apply wOk_match | exact wOk_nil | exact decWList_S12_ok _ _)
def lookup_S12 (k : Nat) (zs : List W) : Nat := (match Nat.blt k 8 with | true => (match Nat.blt k 7 with | true => (match Nat.beq k 6 with | true => (htProbe 1 3 1 15 4 15 2 3 htd_S12_6 hta_S12_6 zs) | false => 0) | false => (match Nat.beq k 7 with | true => (htProbe 1 13 1 54 6 63 5 31 htd_S12_7 hta_S12_7 zs) | false => 0)) | false => (match Nat.blt k 9 with | true => (match Nat.beq k 8 with | true => (htProbe 1 45 7 171 8 255 7 127 htd_S12_8 hta_S12_8 zs) | false => 0) | false => (match Nat.blt k 10 with | true => (match Nat.beq k 9 with | true => (htProbe 1 14 7 55 6 63 6 63 htd_S12_9 hta_S12_9 zs) | false => 0) | false => (match Nat.beq k 10 with | true => (htProbe 1 1 1 5 3 7 2 3 htd_S12_10 hta_S12_10 zs) | false => 0))))
def applyG_S12 (g : Nat) (zs : List W) : List W := match g with
  | 1 => mapInv fixP_S12_1 swP_S12_1 fixN_S12_1 swN_S12_1 zs
  | _ => zs
lemma applyG_S12_sound (g s : Nat) (zs : List W)
    (hrc : ∀ w ∈ zs.map W.toPNT, RowColConst 8 7 w.1 w.2.1)
    (hnat : NatTRestricted (2 ^ (8 * 7) - 1) s (zs.map W.toPNT)) :
    (∀ w ∈ (applyG_S12 g zs).map W.toPNT, RowColConst 8 7 w.1 w.2.1) ∧ NatTRestricted (2 ^ (8 * 7) - 1) s ((applyG_S12 g zs).map W.toPNT) := by
  rcases g with _ | _ | g
  · exact ⟨hrc, hnat⟩
  · exact inv_list_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) hrc hnat
  · exact ⟨hrc, hnat⟩
def certHit_S12 (k : Nat) (zs : List W) : Bool :=
  let code := lookup_S12 k zs
  match Nat.beq code 0 with | true => false | false => let c := Nat.sub code 1; let q := Nat.shiftRight c 1; match Nat.blt q (cnt_S12 k) with | false => false | true => isPermW (applyG_S12 (Nat.land c 1) zs) (decSt_S12 k q)
lemma certHit_S12_sound (s : Nat) (zs : List W)
    (hrc : ∀ w ∈ zs.map W.toPNT, RowColConst 8 7 w.1 w.2.1)
    (hnat : NatTRestricted (2 ^ (8 * 7) - 1) s (zs.map W.toPNT)) (hhit : certHit_S12 s zs = true) :
    ∃ idx < cnt_S12 s, (∀ w ∈ (decSt_S12 s idx).map W.toPNT, RowColConst 8 7 w.1 w.2.1) ∧ NatTRestricted (2 ^ (8 * 7) - 1) s ((decSt_S12 s idx).map W.toPNT) := by
  unfold certHit_S12 at hhit; dsimp only at hhit
  cases h0 : Nat.beq (lookup_S12 s zs) 0 <;> simp only [h0] at hhit
  · cases h1 : Nat.blt (Nat.shiftRight (Nat.sub (lookup_S12 s zs) 1) 1) (cnt_S12 s) <;> simp only [h1] at hhit
    · contradiction
    · have hp := isPermW_sound hhit
      have ⟨h1a, h2a⟩ := applyG_S12_sound (Nat.land (Nat.sub (lookup_S12 s zs) 1) 1) s zs hrc hnat
      exact ⟨_, by simpa [Nat.blt_eq] using h1, fun w hw => h1a w (hp.mem_iff.2 hw), natTRestricted_perm hp h2a⟩
  · contradiction
def chk_S12 (k idx : Nat) : Bool :=
  match stepExpand top_S12 7 m1_S12 m2_S12 m4_S12 m8_S12 rs_S12 rf_S12 certHit_S12 k (decSt_S12 k idx) with | true => false | false => true
lemma c_S12_6_0 : span (chk_S12 6) 2 0 = true := by decide +kernel
lemma all_S12_6 : ∀ i, 0 ≤ i → i < 2 → chk_S12 6 i = true := sr rfl c_S12_6_0
lemma c_S12_7_0 : span (chk_S12 7) 11 0 = true := by decide +kernel
lemma all_S12_7 : ∀ i, 0 ≤ i → i < 11 → chk_S12 7 i = true := sr rfl c_S12_7_0
lemma c_S12_8_0 : span (chk_S12 8) 8 0 = true := by decide +kernel
lemma c_S12_8_1 : span (chk_S12 8) 8 8 = true := by decide +kernel
lemma c_S12_8_2 : span (chk_S12 8) 8 16 = true := by decide +kernel
lemma c_S12_8_3 : span (chk_S12 8) 8 24 = true := by decide +kernel
lemma c_S12_8_4 : span (chk_S12 8) 8 32 = true := by decide +kernel
lemma c_S12_8_5 : span (chk_S12 8) 8 40 = true := by decide +kernel
lemma c_S12_8_6 : span (chk_S12 8) 5 48 = true := by decide +kernel
lemma all_S12_8 : ∀ i, 0 ≤ i → i < 53 → chk_S12 8 i = true := rj (rj (rj (rj (rj (rj (sr rfl c_S12_8_0) (sr rfl c_S12_8_1)) (sr rfl c_S12_8_2)) (sr rfl c_S12_8_3)) (sr rfl c_S12_8_4)) (sr rfl c_S12_8_5)) (sr rfl c_S12_8_6)
lemma c_S12_9_0 : span (chk_S12 9) 8 0 = true := by decide +kernel
lemma c_S12_9_1 : span (chk_S12 9) 8 8 = true := by decide +kernel
lemma c_S12_9_2 : span (chk_S12 9) 8 16 = true := by decide +kernel
lemma all_S12_9 : ∀ i, 0 ≤ i → i < 24 → chk_S12 9 i = true := rj (rj (sr rfl c_S12_9_0) (sr rfl c_S12_9_1)) (sr rfl c_S12_9_2)
lemma c_S12_10_0 : span (chk_S12 10) 2 0 = true := by decide +kernel
lemma all_S12_10 : ∀ i, 0 ≤ i → i < 2 → chk_S12 10 i = true := sr rfl c_S12_10_0
lemma hcheck_S12 : ∀ s ≤ 10, ∀ idx < cnt_S12 s,
    stepExpand (2 ^ (8 * 7) - 1) 7 m1_S12 m2_S12 m4_S12 m8_S12 rs_S12 rf_S12 certHit_S12 s (decSt_S12 s idx) = false := by
  have htop : (2 ^ (8 * 7) - 1) = top_S12 := by decide +kernel
  rw [htop]
  have hfail : ∀ k idx, (∀ i, 0 ≤ i → i < cnt_S12 k → chk_S12 k i = true) → idx < cnt_S12 k →
      stepExpand top_S12 7 m1_S12 m2_S12 m4_S12 m8_S12 rs_S12 rf_S12 certHit_S12 k (decSt_S12 k idx) = false := by
    intro k idx hall hi; have h1 := hall idx (Nat.zero_le _) hi; unfold chk_S12 at h1
    cases hse : stepExpand top_S12 7 m1_S12 m2_S12 m4_S12 m8_S12 rs_S12 rf_S12 certHit_S12 k (decSt_S12 k idx) <;> simp only [hse] at h1
    · rfl
    · contradiction
  intro s hs idx hidx; interval_cases s
  · have h0 : cnt_S12 0 = 0 := rfl; omega
  · have h0 : cnt_S12 1 = 0 := rfl; omega
  · have h0 : cnt_S12 2 = 0 := rfl; omega
  · have h0 : cnt_S12 3 = 0 := rfl; omega
  · have h0 : cnt_S12 4 = 0 := rfl; omega
  · have h0 : cnt_S12 5 = 0 := rfl; omega
  · exact hfail 6 idx all_S12_6 hidx
  · exact hfail 7 idx all_S12_7 hidx
  · exact hfail 8 idx all_S12_8 hidx
  · exact hfail 9 idx all_S12_9 hidx
  · exact hfail 10 idx all_S12_10 hidx
lemma r_S12_0 : searchCert top_S12 7 m1_S12 m2_S12 m4_S12 m8_S12 rs_S12 rf_S12 certHit_S12 9 (mkLitWt top_S12 litW_S12 [2, 0, 2, 0, 2, 2, 2] false) = false := by decide +kernel
lemma r_S12_1 : searchCert top_S12 7 m1_S12 m2_S12 m4_S12 m8_S12 rs_S12 rf_S12 certHit_S12 9 (mkLitWt top_S12 litW_S12 [2, 0, 2, 0, 2, 2, 2] true) = false := by decide +kernel
lemma r_S12_2 : searchCert top_S12 7 m1_S12 m2_S12 m4_S12 m8_S12 rs_S12 rf_S12 certHit_S12 10 (mkLitWt top_S12 litW_S12 [1, 0, 1, 0, 1, 1, 1] false) = false := by decide +kernel
lemma r_S12_3 : searchCert top_S12 7 m1_S12 m2_S12 m4_S12 m8_S12 rs_S12 rf_S12 certHit_S12 10 (mkLitWt top_S12 litW_S12 [1, 0, 1, 0, 1, 1, 1] true) = false := by decide +kernel
lemma no_S12 : ¬ HasMono pos_S12 neg_S12 (initOf vs_S12 true) 10 := by
  have htop : 2 ^ (pos_S12.length * neg_S12.length) - 1 = top_S12 := by decide +kernel
  have hms : checkMasks pos_S12.length neg_S12.length m1_S12 m2_S12 m4_S12 m8_S12 rs_S12 = true := by decide +kernel
  intro h
  obtain ⟨k1, hk1, hm1⟩ := hasMono_to_monoLive (by decide) (by decide) 10 _ h
  obtain ⟨k2, hk2, U, hUW, hUnd, hSU⟩ := monoLive_to_sMonoLive k1 _ hm1
  obtain ⟨hperm, hlen⟩ := classify_U_w9 (by decide) (by decide +kernel) hUW hUnd hSU
  have hk_min : 9 ≤ k2 := by
    by_contra hlt
    have hv : varF 0 ∈ U := by rcases hperm with hp | hp <;> exact hp.mem_iff.2 (by simp [vs_S12])
    have ⟨_, hhm⟩ := one_zero_wire_save_one sub_S12_0.1 k2 U (fun u hu => initOf_mono _ _ u (hUW u hu)) hSU _ hv (by funext x; simp [projV, varF])
    exact sub_S12_0.2 U hUW (hasMono_mono_k (by omega) hhm)
  have hk_le : k2 ≤ 10 := by omega
  have hSub0 : ∀ u ∈ vs_S12.map varF, u ∈ initOf vs_S12 true := fun u hu => by simp [initOf, hu]
  interval_cases k2
  · rcases hperm with hperm | hperm
    ·
      refine close_ht_case (vs := vs_S12) (tgs := [2, 0, 2, 0, 2, 2, 2]) (withW9 := false) (cap := 10) (by decide) (by decide) (by decide) htop hms (by decide) (by decide) encLit_S12 decSt_S12_ok certHit_S12_sound hcheck_S12 (by omega) ?_ (sMonoLive_perm hperm hSU) r_S12_0
      intro wt hwt; simp only [mkWt, vs_S12, List.zipWith_cons_cons, List.zipWith_nil_left, List.append_nil, List.mem_cons, List.not_mem_nil, or_false, ite_false, Bool.false_eq_true] at hwt; rcases hwt with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact tagOk_of_sub sub_S12_0 hSub0 (Or.inr ⟨rfl, by omega⟩)
      · trivial
      · exact tagOk_of_sub sub_S12_2 hSub0 (Or.inr ⟨rfl, by omega⟩)
      · trivial
      · exact tagOk_of_sub sub_S12_6 hSub0 (Or.inr ⟨rfl, by omega⟩)
      · exact tagOk_of_sub sub_S12_7 hSub0 (Or.inr ⟨rfl, by omega⟩)
      · exact tagOk_of_sub sub_S12_8 hSub0 (Or.inr ⟨rfl, by omega⟩)
    ·
      refine close_ht_case (vs := vs_S12) (tgs := [2, 0, 2, 0, 2, 2, 2]) (withW9 := true) (cap := 10) (by decide) (by decide) (by decide) htop hms (by decide) (by decide) encLit_S12 decSt_S12_ok certHit_S12_sound hcheck_S12 (by omega) ?_ (sMonoLive_perm hperm hSU) r_S12_1
      intro wt hwt; simp only [mkWt, vs_S12, List.zipWith_cons_cons, List.zipWith_nil_left, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false, ite_true] at hwt; rcases hwt with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact tagOk_of_sub sub_S12_0 (fun _ h => h) (Or.inr ⟨rfl, by omega⟩)
      · trivial
      · exact tagOk_of_sub sub_S12_2 (fun _ h => h) (Or.inr ⟨rfl, by omega⟩)
      · trivial
      · exact tagOk_of_sub sub_S12_6 (fun _ h => h) (Or.inr ⟨rfl, by omega⟩)
      · exact tagOk_of_sub sub_S12_7 (fun _ h => h) (Or.inr ⟨rfl, by omega⟩)
      · exact tagOk_of_sub sub_S12_8 (fun _ h => h) (Or.inr ⟨rfl, by omega⟩)
      · trivial
  · rcases hperm with hperm | hperm
    ·
      refine close_ht_case (vs := vs_S12) (tgs := [1, 0, 1, 0, 1, 1, 1]) (withW9 := false) (cap := 10) (by decide) (by decide) (by decide) htop hms (by decide) (by decide) encLit_S12 decSt_S12_ok certHit_S12_sound hcheck_S12 (by omega) ?_ (sMonoLive_perm hperm hSU) r_S12_2
      intro wt hwt; simp only [mkWt, vs_S12, List.zipWith_cons_cons, List.zipWith_nil_left, List.append_nil, List.mem_cons, List.not_mem_nil, or_false, ite_false, Bool.false_eq_true] at hwt; rcases hwt with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact tagOk_of_sub sub_S12_0 hSub0 (Or.inl ⟨rfl, by omega⟩)
      · trivial
      · exact tagOk_of_sub sub_S12_2 hSub0 (Or.inl ⟨rfl, by omega⟩)
      · trivial
      · exact tagOk_of_sub sub_S12_6 hSub0 (Or.inl ⟨rfl, by omega⟩)
      · exact tagOk_of_sub sub_S12_7 hSub0 (Or.inl ⟨rfl, by omega⟩)
      · exact tagOk_of_sub sub_S12_8 hSub0 (Or.inl ⟨rfl, by omega⟩)
    ·
      refine close_ht_case (vs := vs_S12) (tgs := [1, 0, 1, 0, 1, 1, 1]) (withW9 := true) (cap := 10) (by decide) (by decide) (by decide) htop hms (by decide) (by decide) encLit_S12 decSt_S12_ok certHit_S12_sound hcheck_S12 (by omega) ?_ (sMonoLive_perm hperm hSU) r_S12_3
      intro wt hwt; simp only [mkWt, vs_S12, List.zipWith_cons_cons, List.zipWith_nil_left, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false, ite_true] at hwt; rcases hwt with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact tagOk_of_sub sub_S12_0 (fun _ h => h) (Or.inl ⟨rfl, by omega⟩)
      · trivial
      · exact tagOk_of_sub sub_S12_2 (fun _ h => h) (Or.inl ⟨rfl, by omega⟩)
      · trivial
      · exact tagOk_of_sub sub_S12_6 (fun _ h => h) (Or.inl ⟨rfl, by omega⟩)
      · exact tagOk_of_sub sub_S12_7 (fun _ h => h) (Or.inl ⟨rfl, by omega⟩)
      · exact tagOk_of_sub sub_S12_8 (fun _ h => h) (Or.inl ⟨rfl, by omega⟩)
      · trivial

-- S11 (V=8, P=9, N=9, w9=1, k=11)
def pos_S11 : List Nat := [3, 6, 17, 33, 66, 132, 160, 288, 320]
def neg_S11 : List Nat := [50, 69, 116, 193, 208, 261, 276, 385, 402]
def vs_S11 : List (Fin 9) := [0, 1, 2, 4, 5, 6, 7, 8]
lemma no_S11 : ¬ HasMono pos_S11 neg_S11 (initOf vs_S11 true) 11 :=
  instant_kill_fast 4 (fun i : Fin 9 => (match i.1 with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8 : Fin 9)) (by decide) (by decide) (by decide +kernel) (by omega)
    (by decide +kernel) (by decide +kernel) (by decide) (by decide) (by decide +kernel) no_S12

-- S15 (V=7, P=8, N=7, w9=1, k=10)
def pos_S15 : List Nat := [3, 6, 12, 33, 132, 160, 264, 288]
def neg_S15 : List Nat := [36, 42, 137, 138, 261, 385, 386]
def vs_S15 : List (Fin 9) := [0, 1, 2, 3, 5, 7, 8]
def top_S15 : Nat := 0xffffffffffffff
def m1_S15 : Nat := 0x7efdfbf7efdfbf
def m2_S15 : Nat := 0x3e7cf9f3e7cf9f
def m4_S15 : Nat := 0xe1c3870e1c387
def m8_S15 : Nat := 0
def rs_S15 : Nat := 0x2040810204081
def rf_S15 : Nat := 127
def litW_S15 : List (Nat × Nat) := [(0xfe0007f, 0x68d1a3468d1a34), (0x3fff, 0x952a54a952a54a), (0x7f01fff80, 0x22448912244891), (0x1fc00001fc000, 0x1c3870e1c3870e), (0xfe03f80fe00000, 0x60c183060c183), (0x3fff0000000, 0xd9b366cd9b366c), (0xfffc0000000000, 0xe1c3870e1c3870), (0xfe03fff, 0xfdfbf7efdfbf7e)]
lemma encLit_S15 : (initOf vs_S15 true).map (fun f => (encPos pos_S15 neg_S15.length f, encNeg pos_S15.length neg_S15 f)) = litW_S15 := by decide +kernel
def pi_S15_0 : Fin 9 → Fin 9 := fun i : Fin 9 => (match i.1 with | 0 => 0 | 1 => 6 | 2 => 8 | 3 => 3 | 4 => 1 | 5 => 7 | 6 => 4 | 7 => 5 | _ => 2 : Fin 9)
lemma sub_S15_0 : SubJust pos_S15 neg_S15 (initOf vs_S15 true) pos_S3 neg_S3 0 pi_S15_0 7 :=
  mkSubJust 0 pi_S15_0 (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) no_S3
def pi_S15_1 : Fin 9 → Fin 9 := fun i : Fin 9 => (match i.1 with | 0 => 6 | 1 => 0 | 2 => 2 | 3 => 7 | 4 => 1 | 5 => 8 | 6 => 4 | 7 => 3 | _ => 5 : Fin 9)
lemma sub_S15_1 : SubJust pos_S15 neg_S15 (initOf vs_S15 true) pos_S3 neg_S3 1 pi_S15_1 7 :=
  mkSubJust 1 pi_S15_1 (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) no_S3
def pi_S15_3 : Fin 9 → Fin 9 := fun i : Fin 9 => (match i.1 with | 0 => 0 | 1 => 1 | 2 => 6 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 4 | 7 => 8 | _ => 7 : Fin 9)
lemma sub_S15_3 : SubJust pos_S15 neg_S15 (initOf vs_S15 true) pos_S13 neg_S13 3 pi_S15_3 7 :=
  mkSubJust 3 pi_S15_3 (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) no_S13
def pi_S15_7 : Fin 9 → Fin 9 := fun i : Fin 9 => (match i.1 with | 0 => 0 | 1 => 1 | 2 => 6 | 3 => 8 | 4 => 2 | 5 => 4 | 6 => 5 | 7 => 7 | _ => 3 : Fin 9)
lemma sub_S15_7 : SubJust pos_S15 neg_S15 (initOf vs_S15 true) pos_S9 neg_S9 7 pi_S15_7 7 :=
  mkSubJust 7 pi_S15_7 (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) no_S9
def pi_S15_8 : Fin 9 → Fin 9 := fun i : Fin 9 => (match i.1 with | 0 => 1 | 1 => 0 | 2 => 5 | 3 => 7 | 4 => 2 | 5 => 6 | 6 => 3 | 7 => 8 | _ => 4 : Fin 9)
lemma sub_S15_8 : SubJust pos_S15 neg_S15 (initOf vs_S15 true) pos_S13 neg_S13 8 pi_S15_8 7 :=
  mkSubJust 8 pi_S15_8 (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) no_S13
def wp_S15 (i : Nat) : Nat := (bn (Nat.blt i 2) (bn (Nat.blt i 1) 0xfffc000fe03fff0000000fe03fff00000000003fff0000000fe03ffffffc0000003f80000007f01fff80fe03f80fe00000000000001fff80fffc07f01fff80fffc00000000000003fff0000000fe03f80fe03fff00000000003fff0000000fe0007ffe03ffffffff8001fc00001fc000 0xfffc00001fc000fe03ffffe03ffffffff80fe0007ffe03f80fe0007ffe03fffffffffffffc000fe0007ffffc0000003fff0003fff01fff800003fff0003fff000007f01fffff0000000fe03fff000007ffffffff0003f80fe00000fe00000fe00000ffffffffe03fff0003ffffe03fff) (bn (Nat.blt i 3) 0xffffffffe0007ffffffff0003ffffffc00001fffff01fc00001ffffffffff80fe00000fe03ffffe00000fffff80fe03fff000007f0003f80fe000000000000fffffff01fff80fffffff0000000fffc07f01ffffffffc07ffffffff01fc07f01fff80ffffffffffff800000000fe00000 0x7f01fc000))
def wn_S15 (i : Nat) : Nat := (bn (Nat.blt i 2) (bn (Nat.blt i 1) 0xfdfbf7efdfbf7e952a54a952a54a0000000000000068d1a3468d1a34e1c3870e1c387022448912244891060c183060c18300000000000000e3c78f1e3c78f1e1c3870e1c3870d9b366cd9b366c972e5cb972e5cb952a54a952a54a68d1a3468d1a34264c993264c9931c3870e1c3870e 0xfdfbf7efdfbf7edfbf7efdfbf7efefdfbf7efdfbf76eddbb76eddbb7b76eddbb76eddbe9d3a74e9d3a74f5ebd7af5ebd7afbf7efdfbf7efdddbb76eddbb76eb76eddbb76eddbfdfbf7efdfbf7e6ad5ab56ad5ab50408102040810204081020408102fdfbf7efdfbf7efdfbf7efdfbf7e) (bn (Nat.blt i 3) 0xf9f3e7cf9f3e7cfdfbf7efdfbf7efdfbf7efdfbf7e9d3a74e9d3a74ee7cf9f3e7cf9f3dfbf7efdfbf7eff7efdfbf7efdfb0000000000000004081020408102fbf7efdfbf7efdf9f3e7cf9f3e7cf7efdfbf7efdfbebd7af5ebd7af53e7cf9f3e7cf9fe7cf9f3e7cf9f304081020408102 0))
def fixP_S15_1 : Nat := 0x1fc000000007f
def swP_S15_1 : List (Nat × Nat) := [(0x7f0000000, 7), (0x3f80, 14), (0x1fc000, 35)]
def fixN_S15_1 : Nat := 0x2040810204081
def swN_S15_1 : List (Nat × Nat) := [(0x10204081020408, 2), (0x4081020408102, 3), (0x8102040810204, 4)]
def st_S15_7 (_ : Nat) : Nat := 0x19153028012436700191510302801247002c150d09280124719150e090402242081c1a15100e0904018
def htd_S15_7 (_ : Nat) : Nat := 0x2600c00
def hta_S15_7 (_ : Nat) : Nat := 0x10000000000008a45273
def st_S15_8 (i : Nat) : Nat := (bn (Nat.blt i 1) 0x901a150e09280124800641c150e092801248008c1a150d0a280124800681c150d0a28012480019150d50280124808001c1a150d09880224800841a150d092801248001c1a150d09040124800541a16100a2802248001a160e0a280224808007c1c150d092802248001978160e09280124800641a151009280124800195c161009280124800541915100a280124800681a150d5028012480019150d500a0401248001915580e500a0124800741a150d0a280124800681a150d7028012480019156c0e092801248681a150d0a042801249641a150e09042801249006019160d09040124800195c165809280124800541915105028012480019160d092801244c8001a150d0928012448800441a160d0928012480040191610092801248003c1a1510092801248001915380e092801248 0x19160d09280224c0800bc1a160d0a28012480019150e0928022420800b81a160e092801248003c1a150e0a2801248006468150e0a280124800b41a150e09280224800641a15b00928022480094ac160d0928012480068ac150d0a280124800941aa80d0928012480060195c0e09280124800a41a150e092801248003c1a150d5028012483c1a150d09042801249005419150d5004012480019160e09280124a080019150e0a280124808001a150d092802249c800941a5c0e09280124800981a160d09280124800941c160d092801248)
def htd_S15_8 (_ : Nat) : Nat := 0x100000000010001000600020000000000030001000000000002010004000000080000000102000006000000000001000000
def hta_S15_8 (i : Nat) : Nat := (bn (Nat.blt i 1) 0x7801a0000011150000000019400000030dd0001216000000000b4f9124011b5000000000028e900a6ba096022de010c03011b0000000003a28017800a30000007a08000c67813570e5b6cdc0000094cbd0e000007e0005000ac0001368b800180e80000000070000008ecb11000001a7 0x1980006e68000009eaa55004e000000000e4000c6000000001dd90000000000170f900324030845c400000530d7c6ca00000000159600cf564e8)
def st_S15_9 (_ : Nat) : Nat := 0x541915580e0928012490054191510092801248541915100e0928012495419a8160d09280124954ac1a150d0928012490019150d092801248085419150d0928012480954641a150e09280124954681a150d0a2801249003c1a150d09280124854195c160e092801249001c1a150d092801248001915100e0928012480019a8160d09280124800641a150e09280124800941a160d09280124800195c160e092801248541c1a150d092801249
def htd_S15_9 (_ : Nat) : Nat := 0x1410c01c308300f011
def hta_S15_9 (_ : Nat) : Nat := 0x74c8631c04400202d80002810240100080c054000f2574c06d448559c79a38435f642886
def st_S15_10 (_ : Nat) : Nat := 0x19150d0928012475419150d092801248
def htd_S15_10 (_ : Nat) : Nat := 0
def hta_S15_10 (_ : Nat) : Nat := 0x130
def decW_S15 (e : Nat) : W :=
  let s := Nat.shiftRight e 2; let c := Nat.shiftRight s 4; let off := Nat.mul (Nat.land s 15) 56
  let p := Nat.land (Nat.shiftRight (wp_S15 c) off) top_S15; let n := Nat.land (Nat.shiftRight (wn_S15 c) off) top_S15
  ⟨p, n, Nat.land e 3, Nat.land p (Nat.xor n top_S15)⟩
def decWList_S15 : Nat → Nat → List W
  | 0, _ => []
  | n + 1, raw => decW_S15 (Nat.land raw 255) :: decWList_S15 n (Nat.shiftRight raw 8)
lemma decWList_S15_ok : ∀ n raw, WOk top_S15 (decWList_S15 n raw)
  | 0, _ => wOk_nil
  | n + 1, raw => wOk_cons rfl (decWList_S15_ok n _)
def cnt_S15 (k : Nat) : Nat := (bn (Nat.blt k 9) (bn (Nat.blt k 8) (bn (Nat.beq k 7) (5) 0) (bn (Nat.beq k 8) (54) 0)) (bn (Nat.blt k 10) (bn (Nat.beq k 9) (18) 0) (bn (Nat.beq k 10) (2) 0)))
def decSt_S15 (k idx : Nat) : List W := (match Nat.blt k 9 with | true => (match Nat.blt k 8 with | true => (match Nat.beq k 7 with | true => (stProbe 68 st_S15_7 decWList_S15 idx) | false => []) | false => (match Nat.beq k 8 with | true => (stProbe 76 st_S15_8 decWList_S15 idx) | false => [])) | false => (match Nat.blt k 10 with | true => (match Nat.beq k 9 with | true => (stProbe 76 st_S15_9 decWList_S15 idx) | false => []) | false => (match Nat.beq k 10 with | true => (stProbe 68 st_S15_10 decWList_S15 idx) | false => [])))
lemma decSt_S15_ok (s idx : Nat) : WOk (2 ^ (8 * 7) - 1) (decSt_S15 s idx) := by
  have htop : (2 ^ (8 * 7) - 1) = top_S15 := by decide +kernel
  rw [htop]; unfold decSt_S15; repeat (first | apply wOk_match | exact wOk_nil | exact decWList_S15_ok _ _)
def lookup_S15 (k : Nat) (zs : List W) : Nat := (match Nat.blt k 9 with | true => (match Nat.blt k 8 with | true => (match Nat.beq k 7 with | true => (htProbe 1 6 1 26 5 31 4 15 htd_S15_7 hta_S15_7 zs) | false => 0) | false => (match Nat.beq k 8 with | true => (htProbe 1 52 1 199 8 255 7 127 htd_S15_8 hta_S15_8 zs) | false => 0)) | false => (match Nat.blt k 10 with | true => (match Nat.beq k 9 with | true => (htProbe 3 12 31 48 6 63 6 63 htd_S15_9 hta_S15_9 zs) | false => 0) | false => (match Nat.beq k 10 with | true => (htProbe 1 1 1 5 3 7 2 3 htd_S15_10 hta_S15_10 zs) | false => 0)))
def applyG_S15 (g : Nat) (zs : List W) : List W := match g with
  | 1 => mapInv fixP_S15_1 swP_S15_1 fixN_S15_1 swN_S15_1 zs
  | _ => zs
lemma applyG_S15_sound (g s : Nat) (zs : List W)
    (hrc : ∀ w ∈ zs.map W.toPNT, RowColConst 8 7 w.1 w.2.1)
    (hnat : NatTRestricted (2 ^ (8 * 7) - 1) s (zs.map W.toPNT)) :
    (∀ w ∈ (applyG_S15 g zs).map W.toPNT, RowColConst 8 7 w.1 w.2.1) ∧ NatTRestricted (2 ^ (8 * 7) - 1) s ((applyG_S15 g zs).map W.toPNT) := by
  rcases g with _ | _ | g
  · exact ⟨hrc, hnat⟩
  · exact inv_list_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) hrc hnat
  · exact ⟨hrc, hnat⟩
def certHit_S15 (k : Nat) (zs : List W) : Bool :=
  let code := lookup_S15 k zs
  match Nat.beq code 0 with | true => false | false => let c := Nat.sub code 1; let q := Nat.shiftRight c 1; match Nat.blt q (cnt_S15 k) with | false => false | true => isPermW (applyG_S15 (Nat.land c 1) zs) (decSt_S15 k q)
lemma certHit_S15_sound (s : Nat) (zs : List W)
    (hrc : ∀ w ∈ zs.map W.toPNT, RowColConst 8 7 w.1 w.2.1)
    (hnat : NatTRestricted (2 ^ (8 * 7) - 1) s (zs.map W.toPNT)) (hhit : certHit_S15 s zs = true) :
    ∃ idx < cnt_S15 s, (∀ w ∈ (decSt_S15 s idx).map W.toPNT, RowColConst 8 7 w.1 w.2.1) ∧ NatTRestricted (2 ^ (8 * 7) - 1) s ((decSt_S15 s idx).map W.toPNT) := by
  unfold certHit_S15 at hhit; dsimp only at hhit
  cases h0 : Nat.beq (lookup_S15 s zs) 0 <;> simp only [h0] at hhit
  · cases h1 : Nat.blt (Nat.shiftRight (Nat.sub (lookup_S15 s zs) 1) 1) (cnt_S15 s) <;> simp only [h1] at hhit
    · contradiction
    · have hp := isPermW_sound hhit
      have ⟨h1a, h2a⟩ := applyG_S15_sound (Nat.land (Nat.sub (lookup_S15 s zs) 1) 1) s zs hrc hnat
      exact ⟨_, by simpa [Nat.blt_eq] using h1, fun w hw => h1a w (hp.mem_iff.2 hw), natTRestricted_perm hp h2a⟩
  · contradiction
def chk_S15 (k idx : Nat) : Bool :=
  match stepExpand top_S15 7 m1_S15 m2_S15 m4_S15 m8_S15 rs_S15 rf_S15 certHit_S15 k (decSt_S15 k idx) with | true => false | false => true
lemma c_S15_7_0 : span (chk_S15 7) 5 0 = true := by decide +kernel
lemma all_S15_7 : ∀ i, 0 ≤ i → i < 5 → chk_S15 7 i = true := sr rfl c_S15_7_0
lemma c_S15_8_0 : span (chk_S15 8) 8 0 = true := by decide +kernel
lemma c_S15_8_1 : span (chk_S15 8) 8 8 = true := by decide +kernel
lemma c_S15_8_2 : span (chk_S15 8) 8 16 = true := by decide +kernel
lemma c_S15_8_3 : span (chk_S15 8) 8 24 = true := by decide +kernel
lemma c_S15_8_4 : span (chk_S15 8) 8 32 = true := by decide +kernel
lemma c_S15_8_5 : span (chk_S15 8) 8 40 = true := by decide +kernel
lemma c_S15_8_6 : span (chk_S15 8) 6 48 = true := by decide +kernel
lemma all_S15_8 : ∀ i, 0 ≤ i → i < 54 → chk_S15 8 i = true := rj (rj (rj (rj (rj (rj (sr rfl c_S15_8_0) (sr rfl c_S15_8_1)) (sr rfl c_S15_8_2)) (sr rfl c_S15_8_3)) (sr rfl c_S15_8_4)) (sr rfl c_S15_8_5)) (sr rfl c_S15_8_6)
lemma c_S15_9_0 : span (chk_S15 9) 8 0 = true := by decide +kernel
lemma c_S15_9_1 : span (chk_S15 9) 8 8 = true := by decide +kernel
lemma c_S15_9_2 : span (chk_S15 9) 2 16 = true := by decide +kernel
lemma all_S15_9 : ∀ i, 0 ≤ i → i < 18 → chk_S15 9 i = true := rj (rj (sr rfl c_S15_9_0) (sr rfl c_S15_9_1)) (sr rfl c_S15_9_2)
lemma c_S15_10_0 : span (chk_S15 10) 2 0 = true := by decide +kernel
lemma all_S15_10 : ∀ i, 0 ≤ i → i < 2 → chk_S15 10 i = true := sr rfl c_S15_10_0
lemma hcheck_S15 : ∀ s ≤ 10, ∀ idx < cnt_S15 s,
    stepExpand (2 ^ (8 * 7) - 1) 7 m1_S15 m2_S15 m4_S15 m8_S15 rs_S15 rf_S15 certHit_S15 s (decSt_S15 s idx) = false := by
  have htop : (2 ^ (8 * 7) - 1) = top_S15 := by decide +kernel
  rw [htop]
  have hfail : ∀ k idx, (∀ i, 0 ≤ i → i < cnt_S15 k → chk_S15 k i = true) → idx < cnt_S15 k →
      stepExpand top_S15 7 m1_S15 m2_S15 m4_S15 m8_S15 rs_S15 rf_S15 certHit_S15 k (decSt_S15 k idx) = false := by
    intro k idx hall hi; have h1 := hall idx (Nat.zero_le _) hi; unfold chk_S15 at h1
    cases hse : stepExpand top_S15 7 m1_S15 m2_S15 m4_S15 m8_S15 rs_S15 rf_S15 certHit_S15 k (decSt_S15 k idx) <;> simp only [hse] at h1
    · rfl
    · contradiction
  intro s hs idx hidx; interval_cases s
  · have h0 : cnt_S15 0 = 0 := rfl; omega
  · have h0 : cnt_S15 1 = 0 := rfl; omega
  · have h0 : cnt_S15 2 = 0 := rfl; omega
  · have h0 : cnt_S15 3 = 0 := rfl; omega
  · have h0 : cnt_S15 4 = 0 := rfl; omega
  · have h0 : cnt_S15 5 = 0 := rfl; omega
  · have h0 : cnt_S15 6 = 0 := rfl; omega
  · exact hfail 7 idx all_S15_7 hidx
  · exact hfail 8 idx all_S15_8 hidx
  · exact hfail 9 idx all_S15_9 hidx
  · exact hfail 10 idx all_S15_10 hidx
lemma r_S15_0 : searchCert top_S15 7 m1_S15 m2_S15 m4_S15 m8_S15 rs_S15 rf_S15 certHit_S15 9 (mkLitWt top_S15 litW_S15 [2, 2, 0, 2, 0, 2, 2] false) = false := by decide +kernel
lemma r_S15_1 : searchCert top_S15 7 m1_S15 m2_S15 m4_S15 m8_S15 rs_S15 rf_S15 certHit_S15 9 (mkLitWt top_S15 litW_S15 [2, 2, 0, 2, 0, 2, 2] true) = false := by decide +kernel
lemma r_S15_2 : searchCert top_S15 7 m1_S15 m2_S15 m4_S15 m8_S15 rs_S15 rf_S15 certHit_S15 10 (mkLitWt top_S15 litW_S15 [1, 1, 0, 1, 0, 1, 1] false) = false := by decide +kernel
lemma r_S15_3 : searchCert top_S15 7 m1_S15 m2_S15 m4_S15 m8_S15 rs_S15 rf_S15 certHit_S15 10 (mkLitWt top_S15 litW_S15 [1, 1, 0, 1, 0, 1, 1] true) = false := by decide +kernel
lemma no_S15 : ¬ HasMono pos_S15 neg_S15 (initOf vs_S15 true) 10 := by
  have htop : 2 ^ (pos_S15.length * neg_S15.length) - 1 = top_S15 := by decide +kernel
  have hms : checkMasks pos_S15.length neg_S15.length m1_S15 m2_S15 m4_S15 m8_S15 rs_S15 = true := by decide +kernel
  intro h
  obtain ⟨k1, hk1, hm1⟩ := hasMono_to_monoLive (by decide) (by decide) 10 _ h
  obtain ⟨k2, hk2, U, hUW, hUnd, hSU⟩ := monoLive_to_sMonoLive k1 _ hm1
  obtain ⟨hperm, hlen⟩ := classify_U_w9 (by decide) (by decide +kernel) hUW hUnd hSU
  have hk_min : 9 ≤ k2 := by
    by_contra hlt
    have hv : varF 0 ∈ U := by rcases hperm with hp | hp <;> exact hp.mem_iff.2 (by simp [vs_S15])
    have ⟨_, hhm⟩ := one_zero_wire_save_one sub_S15_0.1 k2 U (fun u hu => initOf_mono _ _ u (hUW u hu)) hSU _ hv (by funext x; simp [projV, varF])
    exact sub_S15_0.2 U hUW (hasMono_mono_k (by omega) hhm)
  have hk_le : k2 ≤ 10 := by omega
  have hSub0 : ∀ u ∈ vs_S15.map varF, u ∈ initOf vs_S15 true := fun u hu => by simp [initOf, hu]
  interval_cases k2
  · rcases hperm with hperm | hperm
    ·
      refine close_ht_case (vs := vs_S15) (tgs := [2, 2, 0, 2, 0, 2, 2]) (withW9 := false) (cap := 10) (by decide) (by decide) (by decide) htop hms (by decide) (by decide) encLit_S15 decSt_S15_ok certHit_S15_sound hcheck_S15 (by omega) ?_ (sMonoLive_perm hperm hSU) r_S15_0
      intro wt hwt; simp only [mkWt, vs_S15, List.zipWith_cons_cons, List.zipWith_nil_left, List.append_nil, List.mem_cons, List.not_mem_nil, or_false, ite_false, Bool.false_eq_true] at hwt; rcases hwt with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact tagOk_of_sub sub_S15_0 hSub0 (Or.inr ⟨rfl, by omega⟩)
      · exact tagOk_of_sub sub_S15_1 hSub0 (Or.inr ⟨rfl, by omega⟩)
      · trivial
      · exact tagOk_of_sub sub_S15_3 hSub0 (Or.inr ⟨rfl, by omega⟩)
      · trivial
      · exact tagOk_of_sub sub_S15_7 hSub0 (Or.inr ⟨rfl, by omega⟩)
      · exact tagOk_of_sub sub_S15_8 hSub0 (Or.inr ⟨rfl, by omega⟩)
    ·
      refine close_ht_case (vs := vs_S15) (tgs := [2, 2, 0, 2, 0, 2, 2]) (withW9 := true) (cap := 10) (by decide) (by decide) (by decide) htop hms (by decide) (by decide) encLit_S15 decSt_S15_ok certHit_S15_sound hcheck_S15 (by omega) ?_ (sMonoLive_perm hperm hSU) r_S15_1
      intro wt hwt; simp only [mkWt, vs_S15, List.zipWith_cons_cons, List.zipWith_nil_left, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false, ite_true] at hwt; rcases hwt with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact tagOk_of_sub sub_S15_0 (fun _ h => h) (Or.inr ⟨rfl, by omega⟩)
      · exact tagOk_of_sub sub_S15_1 (fun _ h => h) (Or.inr ⟨rfl, by omega⟩)
      · trivial
      · exact tagOk_of_sub sub_S15_3 (fun _ h => h) (Or.inr ⟨rfl, by omega⟩)
      · trivial
      · exact tagOk_of_sub sub_S15_7 (fun _ h => h) (Or.inr ⟨rfl, by omega⟩)
      · exact tagOk_of_sub sub_S15_8 (fun _ h => h) (Or.inr ⟨rfl, by omega⟩)
      · trivial
  · rcases hperm with hperm | hperm
    ·
      refine close_ht_case (vs := vs_S15) (tgs := [1, 1, 0, 1, 0, 1, 1]) (withW9 := false) (cap := 10) (by decide) (by decide) (by decide) htop hms (by decide) (by decide) encLit_S15 decSt_S15_ok certHit_S15_sound hcheck_S15 (by omega) ?_ (sMonoLive_perm hperm hSU) r_S15_2
      intro wt hwt; simp only [mkWt, vs_S15, List.zipWith_cons_cons, List.zipWith_nil_left, List.append_nil, List.mem_cons, List.not_mem_nil, or_false, ite_false, Bool.false_eq_true] at hwt; rcases hwt with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact tagOk_of_sub sub_S15_0 hSub0 (Or.inl ⟨rfl, by omega⟩)
      · exact tagOk_of_sub sub_S15_1 hSub0 (Or.inl ⟨rfl, by omega⟩)
      · trivial
      · exact tagOk_of_sub sub_S15_3 hSub0 (Or.inl ⟨rfl, by omega⟩)
      · trivial
      · exact tagOk_of_sub sub_S15_7 hSub0 (Or.inl ⟨rfl, by omega⟩)
      · exact tagOk_of_sub sub_S15_8 hSub0 (Or.inl ⟨rfl, by omega⟩)
    ·
      refine close_ht_case (vs := vs_S15) (tgs := [1, 1, 0, 1, 0, 1, 1]) (withW9 := true) (cap := 10) (by decide) (by decide) (by decide) htop hms (by decide) (by decide) encLit_S15 decSt_S15_ok certHit_S15_sound hcheck_S15 (by omega) ?_ (sMonoLive_perm hperm hSU) r_S15_3
      intro wt hwt; simp only [mkWt, vs_S15, List.zipWith_cons_cons, List.zipWith_nil_left, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false, ite_true] at hwt; rcases hwt with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact tagOk_of_sub sub_S15_0 (fun _ h => h) (Or.inl ⟨rfl, by omega⟩)
      · exact tagOk_of_sub sub_S15_1 (fun _ h => h) (Or.inl ⟨rfl, by omega⟩)
      · trivial
      · exact tagOk_of_sub sub_S15_3 (fun _ h => h) (Or.inl ⟨rfl, by omega⟩)
      · trivial
      · exact tagOk_of_sub sub_S15_7 (fun _ h => h) (Or.inl ⟨rfl, by omega⟩)
      · exact tagOk_of_sub sub_S15_8 (fun _ h => h) (Or.inl ⟨rfl, by omega⟩)
      · trivial

-- S14 (V=8, P=10, N=9, w9=1, k=12)
def pos_S14 : List Nat := [3, 6, 12, 33, 66, 132, 160, 264, 288, 320]
def neg_S14 : List Nat := [42, 69, 100, 104, 138, 201, 261, 385, 386]
def vs_S14 : List (Fin 9) := [0, 1, 2, 3, 5, 6, 7, 8]
def top_S14 : Nat := 0x3ffffffffffffffffffffff
def m1_S14 : Nat := 0x1feff7fbfdfeff7fbfdfeff
def m2_S14 : Nat := 0xfe7f3f9fcfe7f3f9fcfe7f
def m4_S14 : Nat := 0x3e1f0f87c3e1f0f87c3e1f
def m8_S14 : Nat := 0x201008040201008040201
def rs_S14 : Nat := 0x201008040201008040201
def rf_S14 : Nat := 511
def litW_S14 : List (Nat × Nat) := [(0xff80001ff, 0x1c4e271389c4e271389c4e2), (0x1ff00003ffff, 0x2231188c46231188c462311), (0x3fe00007fffe00, 0x8c46231188c46231188c46), (0xff8000000007fc0000, 0x72391c8e472391c8e47239), (0x1ff007fc0000ff8000000, 0x1a0d068341a0d068341a0d), (0x3fe000000001ff000000000, 0x5c2e170b85c2e170b85c2e), (0x7fffe00000000000, 0x361b0d86c361b0d86c361b0), (0x3ffffff8000000000000000, 0x381c0e070381c0e070381c0), (0x1ffff803ffff, 0x3e7f3f9fcfe7f3f9fcfe7f3)]
lemma encLit_S14 : (initOf vs_S14 true).map (fun f => (encPos pos_S14 neg_S14.length f, encNeg pos_S14.length neg_S14 f)) = litW_S14 := by decide +kernel
def pi_S14_0 : Fin 9 → Fin 9 := fun i : Fin 9 => (match i.1 with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8 : Fin 9)
lemma sub_S14_0 : SubJust pos_S14 neg_S14 (initOf vs_S14 true) pos_S2 neg_S2 0 pi_S14_0 10 :=
  mkSubJust 0 pi_S14_0 (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) no_S2
def pi_S14_3 : Fin 9 → Fin 9 := fun i : Fin 9 => (match i.1 with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8 : Fin 9)
lemma sub_S14_3 : SubJust pos_S14 neg_S14 (initOf vs_S14 true) pos_S12 neg_S12 3 pi_S14_3 10 :=
  mkSubJust 3 pi_S14_3 (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) no_S12
def pi_S14_6 : Fin 9 → Fin 9 := fun i : Fin 9 => (match i.1 with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8 : Fin 9)
lemma sub_S14_6 : SubJust pos_S14 neg_S14 (initOf vs_S14 true) pos_S15 neg_S15 6 pi_S14_6 10 :=
  mkSubJust 6 pi_S14_6 (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) no_S15
def pi_S14_7 : Fin 9 → Fin 9 := fun i : Fin 9 => (match i.1 with | 0 => 1 | 1 => 0 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8 : Fin 9)
lemma sub_S14_7 : SubJust pos_S14 neg_S14 (initOf vs_S14 true) pos_S6 neg_S6 7 pi_S14_7 10 :=
  mkSubJust 7 pi_S14_7 (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) no_S6
def wp_S14 (i : Nat) : Nat := (bn (Nat.blt i 3) (bn (Nat.blt i 1) 0x7fc000000003fe00007fc01ff00003fe00007fffe00007fc0000007fffe00ffffc00000000001ff00003ffff000000000ff803ffffffffc01ff007fffe00ffffffe00007fffe0000003ffff00000000000003fe00fffffffffff8000000007fc000000003ffffff80000000000000000000001ffff80000000000000000000001ffff803ffff000000000ff80001ffff8000000ff8000000007fc0000ff8000000007fffe00ffffc01ff007fc0000ff8000000 (bn (Nat.blt i 2) 0x7fffe00007ffffff0000001ff00000000000000000000003fe00ffffc01ffff8000000007fffe00ffffffe00000000000ff8000000007fffe0000003fe00ff8000000007fc0000ff80001ff007fffe0000003fe0000000000000003fe00ffffc0000ff8000000007fffe00007fc01ff00003fe00ff80001ffff8000000007fc0000007fc000000003fe00ffffc01ff0000001ff00003ffff00000000000003fe00007fc01ff007fffe00000000000 0xffffffe00007fffe00ffffc000000003fe00ffffffe00ff8000000007fffe0000000000000003fe00007ffffff000000000007fffe00ffffc000000003fe00ffffffe0000003fe0000003ffffff803ffffff80001ffff803ffff007fc000000003fe0000000000000003ffff007ffffff007fc01fffffffffffffffc0000ff8000000ffffc0000ffffc0000007fc0000ff803ffffff80001ff00003ffffffffffe00ff80001ffff80001ff007fc01ffff803ffff)) (bn (Nat.blt i 5) (bn (Nat.blt i 4) 0x1ff00003ffffff803fffffffffffffffffffe00000000000ff8000000000000000ff803fffffffffffff00003fe000000001ff000000000000000000000000000000000000ff800000000000000000003fe00000000000fffffffffffffc000000000000000003fe00007fc0000007fffe00ffffc01ff00003fffffffffffff007fc0000ff803ffffffffc0000000000000ff8000000000000000007fffe00ffffc000000003fffffffffffff 0xfffffffff007fffe00fffffffff000000000000000000000000000007fc000000003ffffffffffe00ffffffe00ffffffffffffffffffffffc01ff00003ffff007ffffff007fc00000000000000000000000000000000000001ff007fc000000003fe000000001ffff8000000000000000ffffffe00ff803ffffff8000000000000000ff800000000000000000003fe00ff803ffffff8000000ff8000000fffffffff00003fe00ff8000000ff8000000000000000) (bn (Nat.blt i 6) 0x7fc00000000000000000001ff000000000000000000000000000000000000ff80001ff000000000000000000000000000000000000ff803ffffffffc0000ff803fe00ff80000000000000000000000000000001ff00003fe00007fc01ff00000000000000000000003fe00000000000000000000ff8000000ff8000000007fc0000000000000ffffffe00ffffc01ffffffc000000000000000003fe000000000000000001ffff800000000000000000003ffff 0x1ff007fffe00fffffffff00000000000003fe00000000000000000000ff8000000)))
def wn_S14 (i : Nat) : Nat := (bn (Nat.blt i 3) (bn (Nat.blt i 1) 0x71389c4e271389c4e2713888c46231188c46231188c4688c46231188c46231188c46231188c46231188c46231173399cce673399cce6733989e4f2793c9e4f2793c9e4f1c8e472391c8e472391c8e48c46231188c46231188c46170b85c2e170b85c2e170bb81c0e070381c0e070381c0d86c361b0d86c361b0d86c2231188c46231188c462311231188c46231188c462311872391c8e472391c8e47239170b85c2e170b85c2e170b81a0d068341a0d068341a0d (bn (Nat.blt i 2) 0x71389c4e271389c4e2713885c2e170b85c2e170b85c2e0000000000000000000000072391c8e472391c8e47239e070381c0e070381c0e070361b0d86c361b0d86c361b0170b85c2e170b85c2e170bb61b0d86c361b0d86c361b071389c4e271389c4e27138872391c8e472391c8e47239068341a0d068341a0d0683472391c8e472391c8e4723971389c4e271389c4e27138a231188c46231188c46231171389c4e271389c4e27138b61b0d86c361b0d86c361b0 0xe8f47a3d1e8f47a3d1e8f448c46231188c46231188c46170b85c2e170b85c2e170b88c46231188c46231188c4671389c4e271389c4e2713888e472391c8e472391c8e471c8e472391c8e472391c8e7e7f3f9fcfe7f3f9fcfe7f300804020100804020100806af57abd5eaf57abd5eaf57afd7ebf5fafd7ebf5fafd7c72391c8e472391c8e47239170b85c2e170b85c2e170bba3d1e8f47a3d1e8f47a3d1e371b8dc6e371b8dc6e371a3b1d8ec763b1d8ec763b1d)) (bn (Nat.blt i 5) (bn (Nat.blt i 4) 0x3eff7fbfdfeff7fbfdfeff7e170b85c2e170b85c2e17080804020100804020100804e6f379bcde6f379bcde6f340000000000000000000000000000000000000000000000804020100804020100804fbfdfeff7fbfdfeff7fbfdc8442211088442211088442f9fcfe7f3f9fcfe7f3f9fcfeff7fbfdfeff7fbfdfeff773399cce673399cce6733980201008040201008040201f9fcfe7f3f9fcfe7f3f9fceaf57abd5eaf57abd5eaf57 0xeef77bbddeef77bbddeef740000000000000000000000000000000000000000000039fcfe7f3f9fcfe7f3f9fcfeff7fbfdfeff7fbfdfeff7eaf57abd5eaf57abd5eaf57201008040201008040201000000000000000000000000000000000000000000000000000000000000000000000e3f1f8fc7e3f1f8fc7e3f1c00000000000000000000002190c86432190c86432190f83c1e0f0783c1e0f0783c1e7f3f9fcfe7f3f9fcfe7f3c0000000000000000000000) (bn (Nat.blt i 6) 0x804020100804020100804000804020100804020100804201008040201008040201000201008040201008040201008040201008040201008079bcde6f379bcde6f379bcd000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ebf5fafd7ebf5fafd7ebf5e0100804020100804020100000000000000000000000000000000000000000000000 0x1deef77bbddeef77bbddeef0201008040201008040201383c1e0f0783c1e0f0783c1)))
def st_S14_7 (_ : Nat) : Nat := 0xc058682c140283ce180b0c0582812079c301608080141e0038602c100602808007
def htd_S14_7 (_ : Nat) : Nat := 0
def hta_S14_7 (_ : Nat) : Nat := 0x20000400000600001000
def st_S14_8 (i : Nat) : Nat := (bn (Nat.blt i 2) (bn (Nat.blt i 1) 0x360586046060283c0080c058605c060283c0080c0586046060283c5480c0586046061603c548442102c80230a0141e80c058607c06028f00080c05860461c028f00080c1009046060283c0080c058604606028c85480c058600c05078007480c058905c060283c0080c100903c060283c0080c0586046061c03c00836058604606028c85480c1a0604606028c85480c058605c06028c85480c058604606160c85480c058605c060283c5480c1806046060283c0080c100605c060283c0080c058605c1c0283c0080c058903c1c0283c0080c100603c061403c0080c058903c061403c0080c10060461c1403c0080c05890461c1403c0080c058603c1c1403c0080c058605c061603c5480c1009046061403c0080c058604c060283c0080c10090461c0283c0080c100603c1c0283c008 0xc058684614030141e80c0582046060283c548500602c80160a0141e80c0590010160a0141e80c058602c140283c9c80c0586046060283c0080c0593010160283c008360582046060283c0080c1a02046060283c0080c0582046061603c0080c0586846060283c0080c058204606028c80080c058682c060283c0080c0592810160283c0080c0582046062403c0080c100603c06028f00080c058903c06028f00080c10060461c028f00080c05890461c028f00080c058603c1c028f00080c100604606140f00080c058904606140f00080c058603c06140f00080c058605c061403c0080c058605c06028f00080c058604606029180080c05860461c140f00080c100904606028f00080c0589046061403c0080c058603c1c0283c0080c0589046060283c0080c05860461c0283c008) (bn (Nat.blt i 3) 0xc058605c061603c00836058605c060283c008361a06046060283c008361a0605c060283c0080c058605c580283c0080c05860ac06028c8008361a06046060283c54836058605c060283c5480c1a0605c060283c5480c1a06046061603c5480c058605c06028c8008361a0604606028c800836058605c06028c80080c1a0605c06028c800836058604606160c80080c1a0604606160c80080c058605c06160c8008360586046061603c5480c0593030162403c0080c058202c540283c0080c058202c062403c0080c058602c542403c0080c0586046062903c0080c1002046060283c0080c058203c060283c0080c05820461c0283c0080c0582046061403c0080c058204606028f00080c0582046060283c0080c0586046060903c0080c058602c142403c0080c058202c140283c008 0x361a06046061603c0080c1a0605c060283c0080c058205c060283c0080c058605c5c0283c0080c058605c062403c0080c058605c060296800836058605c061603c0080c1a0605c061603c008))
def htd_S14_8 (i : Nat) : Nat := (bn (Nat.blt i 1) 0x4000000000000000000000000800000000000000000000000000100000000000000100400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000401000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000020000000000000000000000001000000000100000 0x1000000000000000004000000000000000000000000000000000000000000000000000000000)
def hta_S14_8 (i : Nat) : Nat := (bn (Nat.blt i 3) (bn (Nat.blt i 1) 0x1c000002e80017c0000000000000000d2a0001100000000000000000000000000010000000000000000014300000000000000000fa180000128000016ce00000000000000a00000000bc0000000000012c000000000000000000000000010000000000000000000 (bn (Nat.blt i 2) 0x1928800000000000000000000000000000012000000e4000000000000000679200f800000000000000000000000064013008c0000002600000004500000000000000000000000000000000280000000000000000000000000001a0ec800e00000000000000000000000000000000000 0xae000000c0000000700000000000a56044ab8000000000000016c02b0000000a80000000000000002200c6013000000000000005e0000022000000000000000049e803000000000108000000000000f00000000000000000001880000138000027800000000000000000000000000000)) (bn (Nat.blt i 4) 0x1200000000000000000000000000000000000000002c80280000000000000000000010400000029800158000000000000000000000000000000000000000000000000000074000620000d80000000000019800000000000268012a4000000000000000000000234 (bn (Nat.blt i 5) 0x1a000000033000000000000000000008000000016140000000000003a000000000000000058c005e100000000f000002a000010000d4000000000000016360002a8000000000000000000000000b80200000000000000000000000184000c000000000000001180000000000 0xf00470000000000003f000000000000000000000b40000000000000000003000000000000650000000000000000000000000000000000076000006e000000000000)))
def st_S14_9 (i : Nat) : Nat := (bn (Nat.blt i 3) (bn (Nat.blt i 1) 0x620602c8023030141e2a4b1108180b2008c280507a588180b2005828060283d2180b0c08c28060283c9c9000602c302e030141e00400188180b20058280507a030161811818d805078012180b0c08c0c0507800c896a0602c3023030141e0048602c10230a0180a0f002588180b0c08c3805078012a00c058602c140283c009620602c94180b0141e0048602c30160a0141e003224301618119500c05078012180b0c08c386c0283c0090c05860461c0283c00644b50301624118180a0f0024301624118180a0f001912180b0c0780c0507800c89680602c3023030141e004b10301618330180a0f002430164c0408c0c05078012c40c0593080160283c009500602c1023030141e0048602c10180b0180a0f002540180b0c08c0c051e0012180b0c08c0c051e000c89620602c4823030141e004a20301608118180a0f00243016600c08c0c05078012bc0c0586046060283c009 (bn (Nat.blt i 2) 0x501b02c3023030141e004bd0301618118180a0f0025886c0b0c08c0c05078012180b0c0580c05078009c9500602c302e030141e004b70301618170180a0f002540180b260602c05078012a00c058604606028c80090c059001016030141e004b103016080b0180a0f002400180b040580c05078010c40c059005c060283c009620602c80060283c00784b1030164a200580a0f0024301608118180a0f001912c40c0590046060283c009760602c1023030141e0048602c1023030141e003a25a8180b2008c0c05078012c40c1010046060283c0090c0582046060283c007248602c8008118180a0f002540180b200580c05078012180b0408c0c6c0283c009420602c1023030141e0048602c1023030141e00382588180b2008c0c05190012dc0c0582046060283c009620602c80160a0141e004b10301618118180a0f152588180b200602c140283d2a00c059004614030141e9 0xc058603c060283c009048602c301e030141e0039243016180f0180a0f001d12180b0c0780c05078011c90c0586046061403c007e48602c3023030a01e003a24301618118700a0f001d12880c058604606028f0009440602c3023030a01e004a1030161811818500f002430161811818500f001c92180b0c08c0c2807801189360586046060283c00644860d03023030141e003224301618170180a0f001912180b0c08c0c0519000c890c0586046060283c546448602c98180b0141e00322628180b0c08c0c05078012180b0c0580c05078011090c058604606430141e004c20301618118180a0f002608180b0c08c0c05078012180b0c08c0c4807800e890c0586046060283c004e4860803023030141e00322540180b0c08c0c05078012840c0586046062403c0090c0586046062403c007248602c3023031201e00402430161811818900f001f92f80c0586046060283c009)) (bn (Nat.blt i 4) 0x602c4823030141e0040602c4818118180a0f002510180b1208c0c05078012180b0c08c0c051e000e890c1a0604614030141e0048602c302e0a0180a0f0024301618118500c2c078013300c0586046060283c0090c100604614030141e0048602c301e0a0180a0f002430164a0c08c0c05078012180b0c08c0c05078a8009440602c80230a0180a0f48602c30230a0180a0f15243016400c08c0c05078a92000c0586046060283c548420602c8018118500a0f48602c30230a0700a0f0024301618118180a0f001d132c0c0586046060283c0090c0586046060283c007248602c30230e0180a0f002510840b0c08c2805078012840c05860461c0283c009000602c30230e0141e004210301618118180a0f002508180b0c08c0c051e0012180b4a06046060283c0090c058604614030141e0048602c30230e0141e003924301618118192405078012d40c058603c060283c009 (bn (Nat.blt i 5) 0xc1a06046060283c00aa4860d03023030141e003924306818118180a0f002a12880c058605c060283c009001b02c3023030141e004530301618118180a0f00243016185208c0c0507801284360586046060283c009360586046060283c00724a20d81618118180a0f002430161811818580f002012180b0c08c0c2c07801449620602c302e030141e004a20301618118180a320024301618170180a0f002812840c058605c060283c0090c05930302e030141e0048602c302e030141e00392430161817018d805078012180b0c08c0c2c07800e49420602c3023030b01e004a21081640118180a0f0024d8180b0c08c0c05078012180b200604606028c80099e0602c3023030141e004860808018118180a0f00243016401208c0c05078012180b200603c060283c0090c05900302e030141e0048602c30230301478003924301618118180a3c002712180b0c08c0c051e001349 0x180b0c08c0c05078016c90c0586046060283c54724da0301618118180a0f0025d8180b0c0b80c05078012180b0c08c0c05190016490c058604606028c800b04860803023030141e005724301618118180a32001c92180b1208c0c0507800e490c0589046060283c007448602c8018118180a0f0024d81618118180a0f001d1218340c08c0c0507800e890c058605c060283c007448602c3023030b01e003a24301618118180a32001d12180b0c08c0c05078a8e890c1006046060283c00744860803023030141e005624304018118180a0f001c92840c1a06046060283c009)))
def htd_S14_9 (i : Nat) : Nat := (bn (Nat.blt i 1) 0x40000000000000000200000000000000000000000000000000000000000000100000000010000000001000000000000002000000000000000000000000000000000000000000401000010000000001000000000000000000000000000000000000000100c00000000000000000000000000000000000000040000000000000000000000000000000000000000010000000000000000000000000 0x4000000000000000000000000800000000000000000000000040000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000000000000000000)
def hta_S14_9 (i : Nat) : Nat := (bn (Nat.blt i 3) (bn (Nat.blt i 1) 0x300000000000b00000000000000000000000000430000000000133b00002991000087671d755d00aa005f00000000007600006600000000009a000000000000004700000000008a70000000002c000000000000000000000000000000000000006f0000000000000000000000000000000000000000000000007a3d00 (bn (Nat.blt i 2) 0x7b0064320000000000000000009300269d62a900358000310000303c000099000000005900b5001c4c0000000000008e00001a00000000000000000000000000002a000000000000000004ad0000007700000000000000000000ae00008f00006c150000000000000000000000b2835ca50017b110000000000000000001b0 0xe004a009e0000a1000000000097005100815200001900000000000000000023b40000009c05000000007f000000000000000000004500000000000000000000610085000000000000080000954800b3000000008200000000983e0000000000000d7400002b000000004d00002100000000000000000000000000000000007e)) (bn (Nat.blt i 5) (bn (Nat.blt i 4) 0x4b00000000005a005400000014000000000000af0000001b6d1e0000000000a70000000000000000000000000000004200000000005b005e6000000000000000000000000000880000000079005539000020000046a40000000000860000000000000071060000000044890000840900ab00000034964e020000 0x69920000000000000000a200000000000000000000000000008c0f2f00000000000000000000000000000000000018570022000000723a000000000000000000000000000036000000330000000000000000004050000041000000000000000000000000000000000000000000000000004f0000000000000000003700000000) (bn (Nat.blt i 6) 0x49000a000068006b0000250028110ca338002700000000ac003f2400945800007c1200000000a60000a800006e789b000000000000a00000000063167d000000002d0000000000000000000000650000000000008d90000000078b00000000000000000000002e1f0000560000000000000000000000530000006a00009f7300 0)))
def st_S14_10 (i : Nat) : Nat := (bn (Nat.blt i 2) (bn (Nat.blt i 1) 0x624c0301618118180a0f002988180b2506046060283c00a500602c30230a0180a0f0029b8180b2006046060283c00a0c059003023031b00a0f002988180b2610046060283c00a620602c8023030141e00392988180b200602c060283c00a0c059003023030141e00322988180b2008c0c6c0283c00a00280301640118180a0f002400180b2002046060283c00900000301608118180a0f0021b8c40c0590046060283c00a50310301640118180a0f002800180b0c08c0c050780178900530301618118180a0f002510180b0c08c0c0507800e4a420602c3023030141e00392830164c0c08c0c0507800e4a360602c3023030141e003928006c0b0c08c0c0507800e49001b0301618118180a0f00240000360586046060283c00800060d03023030141e00392588180b0c05828060283c00a003103016180b0500a0f0024301618118500c0507800c8a00310301640118500c0507a400180b0c08c0cba0283c009000602c3023030141e005c2400180b0c29046060283c009 0x602c3023030b01e00392400000c0586046061603c008000602c3023030146400392400000c058604606028c80080c0586046060283c5400392800180b0c08c0c05078a8e49420602c3023030141e003a2800000c0586046060283c548760602c3023030141e00392910180b0c08c0c0507800e8a000602c3023030141e2a002401300c0586046060283c009000602c3023032480a0f002400180b2506046060283c009000602c3023030141e005b2400000c0586046061403c0080c058604614030141e003928301618118500c0507800e8a000602c30230301478003a2400000c058604606028f0008004f0301618118180a0f002400180b0c2f846060283c009000602c3023030141e0038243016400c08c0c0507800e4a0c059003023030141e003a2910180b0c08c28060283c00a420602c8018118180a0f002988840c0590046060283c00a003103016400b0180a0f002588180b2008c0c0507800c8a620602c8023030141e003a2800180b0c08c0c860283c009) (bn (Nat.blt i 3) 0x620602c3023030146400392988180b0c08c0c05078a8e4a00310301618118180a0f152400a00c058602c060283c009622203016180b0180a0f002800180b0c0585c060283c00900310301618118180a32002588180b0c08c0c050780178a62530301618118180a0f0029b8180b2606046060283c00a500602c3023030141e003929b8180b0c08c0c0507800e4a621b02c3023030141e00392830164c0c08c0c0507800e8a0c0586046060283c00743929d8180b0c08c0c0507800e8a00060803023030141e003a2400000c1006046060283c0080c058903023030141e003a2800180b1208c0c0507800e8900000306818118180a0f002000000c0589046060283c008000602c301e030141e003a2400000c058603c060283c0080c05860461c030141e003a2800180b0c08c380507800e89000602c30230e0180a0f002400000c05860461c0283c008000602c3023030a01e003a2400180b1206046060283c009000602c302e030141e00392400000c058605c060283c008 (bn (Nat.blt i 4) 0x62220301640118180a0f002800c40c0586046061403c00900600301618118180a0f0025b8ec0c0586046060283c00a760602c3023031b00a0f002988ec0c058602c060283c00a760602c3023030141e00322940180b0c08c0c0507800e8a6e0602c3023030141e003a2988180b0c0580c0507800e8a0c0586046060283c00643a29a8180b0c08c0c0507800e8a62060803023030141e003a2800c40c1006046060283c009620602c4823030141e003a2830161811818d80507800e8a620602c3023030141e00392910180b0c08c0c6c0283c00a0c058604606360141e00392800180b0c08c0c0507800e497c310301618118180a0f002800f80c0586046060283c009003d0301618118180a0f002400180b0c08c0c05078009c9500602c3023031b00a0f002940880c0586046060283c00a00310d81618118180a0f00258818340c08c0c0507800e4a00310306818118180a0f002588180b0c0b80c0507800e4a620602c3023030b01e00392800c40c0586046061603c009 0x31030161811818900f002510180b0c08c0c0507800c8a420602c3023030141e00322830164c0c08c0c0507800c8a0c0586046060283c0064392800180b0c0580c0507800c8900420301618118180a0f002400180b0408c0c0507800c890c058604654030141e00322800180b0c08c0c4807800c890000030161811818900f002000c40c058605c060283c009620602c3016030141e005029b8c40c058602c060283c00a0031030164c0c0580a0f002588180b0c3102c060283c00a620602c3016030141e00612940180b0c08c0c0507800c8a6e0602c3023030141e00322830161811818d80507800c8a620602c3016030141e00322988180b0c0580c0507800e4a00310301624118180a0f002588180b0c0780c0507800e8a003103016180f0180a0f002588180b0c08c380507800e8a00310301618118700a0f002588180b0c08c0c2807800e8a620602c30230301478003a2800c40c058604606028f0009500602c8018118180a0f0029893c0c0586046060283c00a)))
def htd_S14_10 (_ : Nat) : Nat := 0x100c0000008080000000000000008000200000000002000040200038040000010000000008000a00010040400000000201000040c00000040201000000005000000201018000001000000000000080600000000200010040c05000000000
def hta_S14_10 (i : Nat) : Nat := (bn (Nat.blt i 1) 0x1b00000000001f580000000000081a0400000000302c0066000d802d00004b000c003b679f45312700000000931c896300009e0f167402007300004c40009715000000000000000000000065750000004e0000008100002b463d7600838a776f00000078865f7f007e9400193a00110000230012000000649626620b139d351e (bn (Nat.blt i 2) 0x9239066e90480000002972849537009a0032008785000000003f0000000000005b000000980000000000008f007a6c007b8c0025078e7d000000003e0088008b1400705e10000033000000002a6a0e010000000000000009610000002200004300007c8d799b5153682f000000004a52424900821800504f00006000001d0000 0x5910000000000573800569c3c004d2e410000715500004744695a5c000000002800000000000000002417210059000000346b0000035d00a0365400000020000a6d99))
def st_S14_11 (_ : Nat) : Nat := 0x50310301618118180a0f002800a00c0586046060283c00962220301618118180a0f0029b8c40c0586046060283c00a620602c3023031b00a0f002800180b0c08c0c6c0283c00962210301618118180a0f002988180b2606046060283c00a620602c3023030141e00392800c40c058602c060283c009620602c3023030141e00322800180b0c08c0c0507800c89000602c30230a0180a0f002400180b2006046060283c009003b0301618118180a0f002400180b2606046060283c00900210301618118180a0f002400880c0586046060283c009623b0301618118180a0f002988180b0c08c28060283c00a00310301640118180a0f002588180b2006046060283c00a620602c3023030141e003a2800dc0c0586046060283c009
def htd_S14_11 (_ : Nat) : Nat := 0x600201018045
def hta_S14_11 (_ : Nat) : Nat := 0x125be29001a0a006e0b000201473026545c1680b15
def decW_S14 (e : Nat) : W :=
  let s := Nat.shiftRight e 2; let c := Nat.shiftRight s 4; let off := Nat.mul (Nat.land s 15) 90
  let p := Nat.land (Nat.shiftRight (wp_S14 c) off) top_S14; let n := Nat.land (Nat.shiftRight (wn_S14 c) off) top_S14
  ⟨p, n, Nat.land e 3, Nat.land p (Nat.xor n top_S14)⟩
def decWList_S14 : Nat → Nat → List W
  | 0, _ => []
  | n + 1, raw => decW_S14 (Nat.land raw 511) :: decWList_S14 n (Nat.shiftRight raw 9)
lemma decWList_S14_ok : ∀ n raw, WOk top_S14 (decWList_S14 n raw)
  | 0, _ => wOk_nil
  | n + 1, raw => wOk_cons rfl (decWList_S14_ok n _)
def cnt_S14 (k : Nat) : Nat := (bn (Nat.blt k 9) (bn (Nat.blt k 8) (bn (Nat.beq k 7) (4) 0) (bn (Nat.beq k 8) (104) 0)) (bn (Nat.blt k 10) (bn (Nat.beq k 9) (181) 0) (bn (Nat.blt k 11) (bn (Nat.beq k 10) (160) 0) (bn (Nat.beq k 11) (24) 0))))
def decSt_S14 (k idx : Nat) : List W := (match Nat.blt k 9 with | true => (match Nat.blt k 8 with | true => (match Nat.beq k 7 with | true => (stProbe 67 st_S14_7 decWList_S14 idx) | false => []) | false => (match Nat.beq k 8 with | true => (stProbe 76 st_S14_8 decWList_S14 idx) | false => [])) | false => (match Nat.blt k 10 with | true => (match Nat.beq k 9 with | true => (stProbe 85 st_S14_9 decWList_S14 idx) | false => []) | false => (match Nat.blt k 11 with | true => (match Nat.beq k 10 with | true => (stProbe 94 st_S14_10 decWList_S14 idx) | false => []) | false => (match Nat.beq k 11 with | true => (stProbe 94 st_S14_11 decWList_S14 idx) | false => []))))
lemma decSt_S14_ok (s idx : Nat) : WOk (2 ^ (10 * 9) - 1) (decSt_S14 s idx) := by
  have htop : (2 ^ (10 * 9) - 1) = top_S14 := by decide +kernel
  rw [htop]; unfold decSt_S14; repeat (first | apply wOk_match | exact wOk_nil | exact decWList_S14_ok _ _)
def lookup_S14 (k : Nat) (zs : List W) : Nat := (match Nat.blt k 9 with | true => (match Nat.blt k 8 with | true => (match Nat.beq k 7 with | true => (htProbe 1 7 1 29 5 31 3 7 htd_S14_7 hta_S14_7 zs) | false => 0) | false => (match Nat.beq k 8 with | true => (htProbe 1 192 1 725 10 1023 7 127 htd_S14_8 hta_S14_8 zs) | false => 0)) | false => (match Nat.blt k 10 with | true => (match Nat.beq k 9 with | true => (htProbe 1 205 1 774 10 1023 8 255 htd_S14_9 hta_S14_9 zs) | false => 0) | false => (match Nat.blt k 11 with | true => (match Nat.beq k 10 with | true => (htProbe 1 85 3 323 9 511 8 255 htd_S14_10 hta_S14_10 zs) | false => 0) | false => (match Nat.beq k 11 with | true => (htProbe 1 8 1 33 6 63 5 31 htd_S14_11 hta_S14_11 zs) | false => 0))))
def certHit_S14 (k : Nat) (zs : List W) : Bool :=
  let code := lookup_S14 k zs
  match Nat.beq code 0 with | true => false | false => let q := Nat.sub code 1; match Nat.blt q (cnt_S14 k) with | false => false | true => isPermW zs (decSt_S14 k q)
lemma certHit_S14_sound (s : Nat) (zs : List W)
    (hrc : ∀ w ∈ zs.map W.toPNT, RowColConst 10 9 w.1 w.2.1)
    (hnat : NatTRestricted (2 ^ (10 * 9) - 1) s (zs.map W.toPNT)) (hhit : certHit_S14 s zs = true) :
    ∃ idx < cnt_S14 s, (∀ w ∈ (decSt_S14 s idx).map W.toPNT, RowColConst 10 9 w.1 w.2.1) ∧ NatTRestricted (2 ^ (10 * 9) - 1) s ((decSt_S14 s idx).map W.toPNT) := by
  unfold certHit_S14 at hhit; dsimp only at hhit
  cases h0 : Nat.beq (lookup_S14 s zs) 0 <;> simp only [h0] at hhit
  · cases h1 : Nat.blt (Nat.sub (lookup_S14 s zs) 1) (cnt_S14 s) <;> simp only [h1] at hhit
    · contradiction
    · have hp := isPermW_sound hhit
      exact ⟨_, by simpa [Nat.blt_eq] using h1, fun w hw => hrc w (hp.mem_iff.2 hw), natTRestricted_perm hp hnat⟩
  · contradiction
def chk_S14 (k idx : Nat) : Bool :=
  match stepExpand top_S14 9 m1_S14 m2_S14 m4_S14 m8_S14 rs_S14 rf_S14 certHit_S14 k (decSt_S14 k idx) with | true => false | false => true
lemma c_S14_7_0 : span (chk_S14 7) 4 0 = true := by decide +kernel
lemma all_S14_7 : ∀ i, 0 ≤ i → i < 4 → chk_S14 7 i = true := sr rfl c_S14_7_0
lemma c_S14_8_0 : span (chk_S14 8) 24 0 = true := by decide +kernel
lemma c_S14_8_1 : span (chk_S14 8) 24 24 = true := by decide +kernel
lemma c_S14_8_2 : span (chk_S14 8) 24 48 = true := by decide +kernel
lemma c_S14_8_3 : span (chk_S14 8) 24 72 = true := by decide +kernel
lemma c_S14_8_4 : span (chk_S14 8) 8 96 = true := by decide +kernel
lemma all_S14_8 : ∀ i, 0 ≤ i → i < 104 → chk_S14 8 i = true := rj (rj (rj (rj (sr rfl c_S14_8_0) (sr rfl c_S14_8_1)) (sr rfl c_S14_8_2)) (sr rfl c_S14_8_3)) (sr rfl c_S14_8_4)
lemma c_S14_9_0 : span (chk_S14 9) 16 0 = true := by decide +kernel
lemma c_S14_9_1 : span (chk_S14 9) 16 16 = true := by decide +kernel
lemma c_S14_9_2 : span (chk_S14 9) 16 32 = true := by decide +kernel
lemma c_S14_9_3 : span (chk_S14 9) 16 48 = true := by decide +kernel
lemma c_S14_9_4 : span (chk_S14 9) 16 64 = true := by decide +kernel
lemma c_S14_9_5 : span (chk_S14 9) 16 80 = true := by decide +kernel
lemma c_S14_9_6 : span (chk_S14 9) 16 96 = true := by decide +kernel
lemma c_S14_9_7 : span (chk_S14 9) 16 112 = true := by decide +kernel
lemma c_S14_9_8 : span (chk_S14 9) 16 128 = true := by decide +kernel
lemma c_S14_9_9 : span (chk_S14 9) 16 144 = true := by decide +kernel
lemma c_S14_9_10 : span (chk_S14 9) 16 160 = true := by decide +kernel
lemma c_S14_9_11 : span (chk_S14 9) 5 176 = true := by decide +kernel
lemma all_S14_9 : ∀ i, 0 ≤ i → i < 181 → chk_S14 9 i = true := rj (rj (rj (rj (rj (rj (rj (rj (rj (rj (rj (sr rfl c_S14_9_0) (sr rfl c_S14_9_1)) (sr rfl c_S14_9_2)) (sr rfl c_S14_9_3)) (sr rfl c_S14_9_4)) (sr rfl c_S14_9_5)) (sr rfl c_S14_9_6)) (sr rfl c_S14_9_7)) (sr rfl c_S14_9_8)) (sr rfl c_S14_9_9)) (sr rfl c_S14_9_10)) (sr rfl c_S14_9_11)
lemma c_S14_10_0 : span (chk_S14 10) 8 0 = true := by decide +kernel
lemma c_S14_10_1 : span (chk_S14 10) 8 8 = true := by decide +kernel
lemma c_S14_10_2 : span (chk_S14 10) 8 16 = true := by decide +kernel
lemma c_S14_10_3 : span (chk_S14 10) 8 24 = true := by decide +kernel
lemma c_S14_10_4 : span (chk_S14 10) 8 32 = true := by decide +kernel
lemma c_S14_10_5 : span (chk_S14 10) 8 40 = true := by decide +kernel
lemma c_S14_10_6 : span (chk_S14 10) 8 48 = true := by decide +kernel
lemma c_S14_10_7 : span (chk_S14 10) 8 56 = true := by decide +kernel
lemma c_S14_10_8 : span (chk_S14 10) 8 64 = true := by decide +kernel
lemma c_S14_10_9 : span (chk_S14 10) 8 72 = true := by decide +kernel
lemma c_S14_10_10 : span (chk_S14 10) 8 80 = true := by decide +kernel
lemma c_S14_10_11 : span (chk_S14 10) 8 88 = true := by decide +kernel
lemma c_S14_10_12 : span (chk_S14 10) 8 96 = true := by decide +kernel
lemma c_S14_10_13 : span (chk_S14 10) 8 104 = true := by decide +kernel
lemma c_S14_10_14 : span (chk_S14 10) 8 112 = true := by decide +kernel
lemma c_S14_10_15 : span (chk_S14 10) 8 120 = true := by decide +kernel
lemma c_S14_10_16 : span (chk_S14 10) 8 128 = true := by decide +kernel
lemma c_S14_10_17 : span (chk_S14 10) 8 136 = true := by decide +kernel
lemma c_S14_10_18 : span (chk_S14 10) 8 144 = true := by decide +kernel
lemma c_S14_10_19 : span (chk_S14 10) 8 152 = true := by decide +kernel
lemma all_S14_10 : ∀ i, 0 ≤ i → i < 160 → chk_S14 10 i = true := rj (rj (rj (rj (rj (rj (rj (rj (rj (rj (rj (rj (rj (rj (rj (rj (rj (rj (rj (sr rfl c_S14_10_0) (sr rfl c_S14_10_1)) (sr rfl c_S14_10_2)) (sr rfl c_S14_10_3)) (sr rfl c_S14_10_4)) (sr rfl c_S14_10_5)) (sr rfl c_S14_10_6)) (sr rfl c_S14_10_7)) (sr rfl c_S14_10_8)) (sr rfl c_S14_10_9)) (sr rfl c_S14_10_10)) (sr rfl c_S14_10_11)) (sr rfl c_S14_10_12)) (sr rfl c_S14_10_13)) (sr rfl c_S14_10_14)) (sr rfl c_S14_10_15)) (sr rfl c_S14_10_16)) (sr rfl c_S14_10_17)) (sr rfl c_S14_10_18)) (sr rfl c_S14_10_19)
lemma c_S14_11_0 : span (chk_S14 11) 8 0 = true := by decide +kernel
lemma c_S14_11_1 : span (chk_S14 11) 8 8 = true := by decide +kernel
lemma c_S14_11_2 : span (chk_S14 11) 8 16 = true := by decide +kernel
lemma all_S14_11 : ∀ i, 0 ≤ i → i < 24 → chk_S14 11 i = true := rj (rj (sr rfl c_S14_11_0) (sr rfl c_S14_11_1)) (sr rfl c_S14_11_2)
lemma hcheck_S14 : ∀ s ≤ 12, ∀ idx < cnt_S14 s,
    stepExpand (2 ^ (10 * 9) - 1) 9 m1_S14 m2_S14 m4_S14 m8_S14 rs_S14 rf_S14 certHit_S14 s (decSt_S14 s idx) = false := by
  have htop : (2 ^ (10 * 9) - 1) = top_S14 := by decide +kernel
  rw [htop]
  have hfail : ∀ k idx, (∀ i, 0 ≤ i → i < cnt_S14 k → chk_S14 k i = true) → idx < cnt_S14 k →
      stepExpand top_S14 9 m1_S14 m2_S14 m4_S14 m8_S14 rs_S14 rf_S14 certHit_S14 k (decSt_S14 k idx) = false := by
    intro k idx hall hi; have h1 := hall idx (Nat.zero_le _) hi; unfold chk_S14 at h1
    cases hse : stepExpand top_S14 9 m1_S14 m2_S14 m4_S14 m8_S14 rs_S14 rf_S14 certHit_S14 k (decSt_S14 k idx) <;> simp only [hse] at h1
    · rfl
    · contradiction
  intro s hs idx hidx; interval_cases s
  · have h0 : cnt_S14 0 = 0 := rfl; omega
  · have h0 : cnt_S14 1 = 0 := rfl; omega
  · have h0 : cnt_S14 2 = 0 := rfl; omega
  · have h0 : cnt_S14 3 = 0 := rfl; omega
  · have h0 : cnt_S14 4 = 0 := rfl; omega
  · have h0 : cnt_S14 5 = 0 := rfl; omega
  · have h0 : cnt_S14 6 = 0 := rfl; omega
  · exact hfail 7 idx all_S14_7 hidx
  · exact hfail 8 idx all_S14_8 hidx
  · exact hfail 9 idx all_S14_9 hidx
  · exact hfail 10 idx all_S14_10 hidx
  · exact hfail 11 idx all_S14_11 hidx
  · have h0 : cnt_S14 12 = 0 := rfl; omega
lemma r_S14_0 : searchCert top_S14 9 m1_S14 m2_S14 m4_S14 m8_S14 rs_S14 rf_S14 certHit_S14 12 (mkLitWt top_S14 litW_S14 [2, 0, 0, 2, 0, 2, 2, 0] false) = false := by decide +kernel
lemma r_S14_1 : searchCert top_S14 9 m1_S14 m2_S14 m4_S14 m8_S14 rs_S14 rf_S14 certHit_S14 12 (mkLitWt top_S14 litW_S14 [2, 0, 0, 2, 0, 2, 2, 0] true) = false := by decide +kernel
lemma no_S14 : ¬ HasMono pos_S14 neg_S14 (initOf vs_S14 true) 12 := by
  have htop : 2 ^ (pos_S14.length * neg_S14.length) - 1 = top_S14 := by decide +kernel
  have hms : checkMasks pos_S14.length neg_S14.length m1_S14 m2_S14 m4_S14 m8_S14 rs_S14 = true := by decide +kernel
  intro h
  obtain ⟨k1, hk1, hm1⟩ := hasMono_to_monoLive (by decide) (by decide) 12 _ h
  obtain ⟨k2, hk2, U, hUW, hUnd, hSU⟩ := monoLive_to_sMonoLive k1 _ hm1
  obtain ⟨hperm, hlen⟩ := classify_U_w9 (by decide) (by decide +kernel) hUW hUnd hSU
  have hk_min : 12 ≤ k2 := by
    by_contra hlt
    have hv : varF 0 ∈ U := by rcases hperm with hp | hp <;> exact hp.mem_iff.2 (by simp [vs_S14])
    have ⟨_, hhm⟩ := one_zero_wire_save_one sub_S14_0.1 k2 U (fun u hu => initOf_mono _ _ u (hUW u hu)) hSU _ hv (by funext x; simp [projV, varF])
    exact sub_S14_0.2 U hUW (hasMono_mono_k (by omega) hhm)
  have hk_le : k2 ≤ 12 := by omega
  have hSub0 : ∀ u ∈ vs_S14.map varF, u ∈ initOf vs_S14 true := fun u hu => by simp [initOf, hu]
  have hk_eq : k2 = 12 := by omega
  subst hk_eq
  rcases hperm with hperm | hperm
  ·
    refine close_ht_case (vs := vs_S14) (tgs := [2, 0, 0, 2, 0, 2, 2, 0]) (withW9 := false) (cap := 12) (by decide) (by decide) (by decide) htop hms (by decide) (by decide) encLit_S14 decSt_S14_ok certHit_S14_sound hcheck_S14 (by omega) ?_ (sMonoLive_perm hperm hSU) r_S14_0
    intro wt hwt; simp only [mkWt, vs_S14, List.zipWith_cons_cons, List.zipWith_nil_left, List.append_nil, List.mem_cons, List.not_mem_nil, or_false, ite_false, Bool.false_eq_true] at hwt; rcases hwt with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact tagOk_of_sub sub_S14_0 hSub0 (Or.inr ⟨rfl, by omega⟩)
    · trivial
    · trivial
    · exact tagOk_of_sub sub_S14_3 hSub0 (Or.inr ⟨rfl, by omega⟩)
    · trivial
    · exact tagOk_of_sub sub_S14_6 hSub0 (Or.inr ⟨rfl, by omega⟩)
    · exact tagOk_of_sub sub_S14_7 hSub0 (Or.inr ⟨rfl, by omega⟩)
    · trivial
  ·
    refine close_ht_case (vs := vs_S14) (tgs := [2, 0, 0, 2, 0, 2, 2, 0]) (withW9 := true) (cap := 12) (by decide) (by decide) (by decide) htop hms (by decide) (by decide) encLit_S14 decSt_S14_ok certHit_S14_sound hcheck_S14 (by omega) ?_ (sMonoLive_perm hperm hSU) r_S14_1
    intro wt hwt; simp only [mkWt, vs_S14, List.zipWith_cons_cons, List.zipWith_nil_left, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false, ite_true] at hwt; rcases hwt with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact tagOk_of_sub sub_S14_0 (fun _ h => h) (Or.inr ⟨rfl, by omega⟩)
    · trivial
    · trivial
    · exact tagOk_of_sub sub_S14_3 (fun _ h => h) (Or.inr ⟨rfl, by omega⟩)
    · trivial
    · exact tagOk_of_sub sub_S14_6 (fun _ h => h) (Or.inr ⟨rfl, by omega⟩)
    · exact tagOk_of_sub sub_S14_7 (fun _ h => h) (Or.inr ⟨rfl, by omega⟩)
    · trivial
    · trivial

-- S16 (V=8, P=10, N=9, w9=1, k=12)
def pos_S16 : List Nat := [3, 6, 12, 17, 24, 33, 66, 264, 288, 320]
def neg_S16 : List Nat := [42, 50, 69, 73, 104, 116, 261, 274, 276]
def vs_S16 : List (Fin 9) := [0, 1, 2, 3, 4, 5, 6, 8]
def top_S16 : Nat := 0x3ffffffffffffffffffffff
def m1_S16 : Nat := 0x1feff7fbfdfeff7fbfdfeff
def m2_S16 : Nat := 0xfe7f3f9fcfe7f3f9fcfe7f
def m4_S16 : Nat := 0x3e1f0f87c3e1f0f87c3e1f
def m8_S16 : Nat := 0x201008040201008040201
def rs_S16 : Nat := 0x201008040201008040201
def rf_S16 : Nat := 511
def litW_S16 : List (Nat × Nat) := [(0x3fe00ff80001ff, 0x984c26130984c26130984c), (0x7fc000000003ffff, 0x1068341a0d068341a0d0683), (0x7fffe00, 0x2c964b2592c964b2592c964), (0xff80001ff007fc0000, 0x32190c86432190c8643219), (0x1ffff8000000, 0x345a2d168b45a2d168b45a2), (0x1ff00003fe00000000000, 0x6633198cc6633198cc6633), (0x3fe00007fc0000000000000, 0x783c1e0f0783c1e0f0783c), (0x3ffffff8000000000000000, 0x381c0e070381c0e070381c0), (0x7fffe00ff803ffff, 0x19ecf67b3d9ecf67b3d9ecf)]
lemma encLit_S16 : (initOf vs_S16 true).map (fun f => (encPos pos_S16 neg_S16.length f, encNeg pos_S16.length neg_S16 f)) = litW_S16 := by decide +kernel
def pi_S16_2 : Fin 9 → Fin 9 := fun i : Fin 9 => (match i.1 with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8 : Fin 9)
lemma sub_S16_2 : SubJust pos_S16 neg_S16 (initOf vs_S16 true) pos_S6 neg_S6 2 pi_S16_2 10 :=
  mkSubJust 2 pi_S16_2 (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) no_S6
def pi_S16_4 : Fin 9 → Fin 9 := fun i : Fin 9 => (match i.1 with | 0 => 1 | 1 => 0 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8 : Fin 9)
lemma sub_S16_4 : SubJust pos_S16 neg_S16 (initOf vs_S16 true) pos_S6 neg_S6 4 pi_S16_4 10 :=
  mkSubJust 4 pi_S16_4 (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) no_S6
def pi_S16_5 : Fin 9 → Fin 9 := fun i : Fin 9 => (match i.1 with | 0 => 1 | 1 => 0 | 2 => 5 | 3 => 8 | 4 => 6 | 5 => 2 | 6 => 4 | 7 => 7 | _ => 3 : Fin 9)
lemma sub_S16_5 : SubJust pos_S16 neg_S16 (initOf vs_S16 true) pos_S6 neg_S6 5 pi_S16_5 10 :=
  mkSubJust 5 pi_S16_5 (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) no_S6
def pi_S16_6 : Fin 9 → Fin 9 := fun i : Fin 9 => (match i.1 with | 0 => 0 | 1 => 1 | 2 => 6 | 3 => 8 | 4 => 5 | 5 => 4 | 6 => 2 | 7 => 7 | _ => 3 : Fin 9)
lemma sub_S16_6 : SubJust pos_S16 neg_S16 (initOf vs_S16 true) pos_S6 neg_S6 6 pi_S16_6 10 :=
  mkSubJust 6 pi_S16_6 (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) no_S6
def wp_S16 (i : Nat) : Nat := (bn (Nat.blt i 1) 0x7fffe00007fc0000007fc0000ff803ffff00003fe00007fffe00000000000ff80001ffff80001ffffffffe00000000000007fc0000000000000007fffe000000001ff000000000ffffffe00ffffc0000000000000ffffffe000000000000000000000000001ffff800000000003fe000000001ffff8000000ffffc000000003ffff000000000ff803fe00007fffe00007fc0000000000000007fc0000ff8000000000000000ff80001ff007fc0000 (bn (Nat.blt i 2) 0xfffffffffff803fe00fffffffffffffc000000003ffff0000001ff000000000ffffc0000ffffffffffffffffffffffffe00007fc01ff000000000ff800000000000000000003fe00fffffffff007fc0000ffffffe00ff803ffff000000000000000000ffffc0000007fffe00ff803ffff0000000000000001ff0000000000000000000000001ff00003fe00007fc01ff007fc0000ff803fe00ff80001ff0000000000000001ffffffffe00007fc00000000001ff 0xfffffffff007fc01ffffffc000000000000000003fe0000003fe000000001ff000000000ff800000000000000000003ffff007fc01fffffffffffff803fe00ff80001ff000000000000000000007fc0000ff8000000000000000ffffffffffffffffffffffc0000ff803fe00ff80001ff))
def wn_S16 (i : Nat) : Nat := (bn (Nat.blt i 1) 0xd168b45a2d168b45a2d1689068341a0d068341a0d0683d168b45a2d168b45a2d168b45a2d168b45a2d168b45a2e070381c0e070381c0e0702c964b2592c964b2592c96441a0d068341a0d068341a0c783c1e0f0783c1e0f0783ce070381c0e070381c0e070345a2d168b45a2d168b45a2b2592c964b2592c964b2591068341a0d068341a0d068326130984c26130984c26130783c1e0f0783c1e0f0783c198cc6633198cc6633198cc32190c86432190c8643219 (bn (Nat.blt i 2) 0xe7f3f9fcfe7f3f9fcfe7f3f87c3e1f0f87c3e1f0f87c345a2d168b45a2d168b45a2dbedf6fb7dbedf6fb7dbedfecf67b3d9ecf67b3d9ecf6400000000000000000000002e974ba5d2e974ba5d2e9759ecf67b3d9ecf67b3d9ecf000000000000000000000019ecf67b3d9ecf67b3d9ecf0000000000000000000000000000000000000000000000c86432190c86432190c864984c26130984c26130984cb2592c964b2592c964b2590783c1e0f0783c1e0f0783c 0xedf6fb7dbedf6fb7dbedf6c00000000000000000000000000000000000000000000002010080402010080402014da6d369b4da6d369b4da6f99cce673399cce673399cc008040201008040201008041209048241209048241209eff7fbfdfeff7fbfdfeff7c9a4d269349a4d269349a4d))
def fixP_S16_1 : Nat := 0xff80000000000001ff
def swP_S16_1 : List (Nat × Nat) := [(0xff8000000, 18), (0x1ff000000000, 36), (0x3fe00, 45), (0x7fc0000, 63)]
def fixN_S16_1 : Nat := 0x4c26130984c26130984c26
def swN_S16_1 : List (Nat × Nat) := [(0x1008040201008040201008, 3), (0x2010080402010080402010, 4), (0x201008040201008040201, 7)]
def fixP_S16_2 : Nat := 0xff80000000000001ff
def swP_S16_2 : List (Nat × Nat) := [(0x1ff00003fe00000000000, 9), (0x7fffe00, 18)]
def fixN_S16_2 : Nat := 0x26130984c26130984c26130
def swN_S16_2 : List (Nat × Nat) := [(0x8442211088442211088442, 1), (0x201008040201008040201, 3)]
def fixP_S16_3 : Nat := 0xff80000000000001ff
def swP_S16_3 : List (Nat × Nat) := [(0xff8000000, 27), (0x3fe00, 36), (0x1ff000000000, 45), (0x7fc0000, 54)]
def fixN_S16_3 : Nat := 0x4020100804020100804020
def swN_S16_3 : List (Nat × Nat) := [(0x402010080402010080402, 1), (0x30180c06030180c0603018, 4), (0x201008040201008040201, 6)]
def st_S16_8 (_ : Nat) : Nat := 0x2c3c2a240c40060082c1a44240c40060082c3c2a240c0a064c82c1a2a240c40060081c1a44100c0a060081c3c2a100c0a060082c1a2a100c0a060081c3414100c0a060081c342a10480a060081c3c44240c40060081c3c2a380c0a060081c342a100c20060081c342a240c0a060081c342a100c0a060081c3c2a240c0a060082c1a2a240c0a060082c3c2a240c0a060081c1a2a100c0a060081c3414240c20060081c342a380c0a060082c342a240c0a060081c302a240c0a060082c1a2a240c20060081c1a14100c0a06008
def htd_S16_8 (_ : Nat) : Nat := 0x4000000000101000100000500020004000103000000000006030005040003000900000400
def hta_S16_8 (i : Nat) : Nat := (bn (Nat.blt i 1) 0x32000320000000000138568018800001682005c0000098037000000000000000154000bac00607e0000000000006a0003e0074043723e080b7240d49f71e071400000000000954000000001d8001612805e000000000000000002eae4cad900000518b1eb3d00600008c027110000000 0x3f3548d102e003426e98c5088f4a)
def st_S16_9 (i : Nat) : Nat := (bn (Nat.blt i 1) 0x1c3c2a70240c0a060097c1c3c2a240c0a060097c2c1a2a240c0a060091c342a70240c0a060097c1c342a240c0a06009781c1a2a740c0a060091c1a2a70100c0a060092c3c2a58240c0a060092c1a2a58240c40060091c342a60240c0a060091c342a58100c0a060091c1a1458100c0a060096c1c3c2a240c0a060096c2c1a2a240c0a060091c3c2a240c0a06006892c1a2a240c0a06006892c1a2a58240c0a060091c1a2a60240c0a060091c1a2a58100c0a060091c1a2a24640c0a060091c1a2a100c0a06005091c1a2a60100c0a060091c1a44240c0a06005c91c3c2a58240c0a060091c3c2a240c0a06005091c1a44240c0a06005491c3c2a240c0a064c0091c1a2a240c40064c0092c3c2a240c0a0600509002c3c2a240c0a060082c1a2a240c400600509002c1a2a240c4006008 0x1c1a14240c0a0600a091c342a58240c0a060091c342a240c0a06005096c1c342a240c0a060091c342a240c0a06006891c1a14240c0a06009c9001c1a14100c0a060081c342a24480c0a060091c1a14100c0a0600689001c342a100c0a060081c1a1424480c0a060091c342a100c0a06006891c1a2a100c0a06009891c1a2a240c0a060068990781a2a940c0a06009782c1a2a240c0a060091c1a2a70240c0a060091c1a2a94100c0a060091c1a2a10640c0a060091c1a1424640c0a060091c342a24640c0a06009901c3c2a240c0a060096c1c1a2a100c0a060091c3c2a24640c0a060092c1a2a24640c0a060091c1a2a240c0a064c8c91c1a2a240c0a0600889841c1a2a240c0a060091c1a2a24800c0a06009)
def htd_S16_9 (_ : Nat) : Nat := 0x4010080400000300000000080408000080004000000802000281000050000014000100c0000000080002000080200010000005008000a00000080200000000400000000800000100807008100200008000605000040000
def hta_S16_9 (i : Nat) : Nat := (bn (Nat.blt i 1) 0x214f6e00ca0000000000d500350000173724000000000000000000000000c9e1070000000008ba0bb2423100700000004100000090000000ea3976461b050db7000000007100bc000000000000000023b67a00000000a74873c1450000000000000000aa009d00ec9300000056000000000084000000b0006500f3 (bn (Nat.blt i 2) 0xbd55600000272d000000004a7f1dbb32e5b15d53c6ceee516c2f6100004e0000004900ae1300e7005c0059b814008d006da100008a00a53300000000039ed200da7591f05b00990000004d50000000003e0011d604157963cd9bc5ed95ef00d300000068296622a93d81d9afdb00d101090000008ec2002b00000000000000 0xe60f7c7de90000000000000000000000ad0000df676b0052eb82cb00475a008900b5008500000000000000e800005f0000))
def st_S16_10 (i : Nat) : Nat := (bn (Nat.blt i 1) 0x1c1a2a7058240c0a0600a1c3c2a58240c0a060050a001c3c2a58240c0a060092c1a2a58240c0a060050a1c1a2a58240c0a064c00a002c1a2a58240c0a060091c1a2a58100c0a060068a001c3c2a240c0a06005091c342a58240c0a060068a001c342a58240c0a0600900a41c1a2a240c0a06009001c1a2a240c0a06009891c1a2a7024640c0a0600a001c1a2a70240c0a06009001c1a2a240c0a06008c91c1a2a5824640c0a0600a1c1a2a24640c0a060050a6c1c1a2a24640c0a0600a1c1a2a24640c0a060068a00001c3c2a240c0a060081c1a2a240c0a064c0050a002c1a2a240c0a0600509001c1a2a240c0a064c00900002c1a2a240c0a060086c1c1a2a240c0a060050a1c1a2a240c0a06006850a1c1a2a24480c0a060068a001c1a2a100c0a0600689001c1a2a24480c0a0600900001c1a2a100c0a06008001c342a240c0a060068900001c342a240c0a06008 0x7c1c1a2a24640c0a0600a1c1a2a70240c0a060050a6c1c1a2a70240c0a0600a1c1a2a70240c0a060068aa41c1a2a58240c0a0600a)
def htd_S16_10 (_ : Nat) : Nat := 0x504000001020000000400030603000000010100000100040201000500000300000000000a01
def hta_S16_10 (i : Nat) : Nat := (bn (Nat.blt i 1) 0x6007a030076005b45612a4131891d227500000000171385190067003c590b000f342908644921603f91694f000000440000436d55041100815c6500008e0009264a8307927e0054353e005e000d32420079024d3d725a6a630000337b050077005d00003b008d713801007d0000377c000078008a94400000000000002d2e25 0x863a0000000000395f156e365700006200)
def st_S16_11 (_ : Nat) : Nat := 0x6c1c1a2a58240c0a0600a1c1a2a58240c0a060068a1c1a2a7058240c0a0600a001c1a2a70240c0a060091c1a2a5824640c0a0600a001c1a2a58240c0a06009006c1c1a2a240c0a06009001c1a2a24640c0a06009
def htd_S16_11 (_ : Nat) : Nat := 0x138005
def hta_S16_11 (_ : Nat) : Nat := 0x7412ac065cd920044010080f6b804
def st_S16_12 (_ : Nat) : Nat := 0x1c1a2a240c0a06008
def htd_S16_12 (_ : Nat) : Nat := 0
def hta_S16_12 (_ : Nat) : Nat := 0x4
def decW_S16 (e : Nat) : W :=
  let s := Nat.shiftRight e 2; let c := Nat.shiftRight s 4; let off := Nat.mul (Nat.land s 15) 90
  let p := Nat.land (Nat.shiftRight (wp_S16 c) off) top_S16; let n := Nat.land (Nat.shiftRight (wn_S16 c) off) top_S16
  ⟨p, n, Nat.land e 3, Nat.land p (Nat.xor n top_S16)⟩
def decWList_S16 : Nat → Nat → List W
  | 0, _ => []
  | n + 1, raw => decW_S16 (Nat.land raw 255) :: decWList_S16 n (Nat.shiftRight raw 8)
lemma decWList_S16_ok : ∀ n raw, WOk top_S16 (decWList_S16 n raw)
  | 0, _ => wOk_nil
  | n + 1, raw => wOk_cons rfl (decWList_S16_ok n _)
def cnt_S16 (k : Nat) : Nat := (bn (Nat.blt k 10) (bn (Nat.blt k 9) (bn (Nat.beq k 8) (24) 0) (bn (Nat.beq k 9) (61) 0)) (bn (Nat.blt k 11) (bn (Nat.beq k 10) (37) 0) (bn (Nat.blt k 12) (bn (Nat.beq k 11) (8) 0) (bn (Nat.beq k 12) (1) 0))))
def decSt_S16 (k idx : Nat) : List W := (match Nat.blt k 10 with | true => (match Nat.blt k 9 with | true => (match Nat.beq k 8 with | true => (stProbe 68 st_S16_8 decWList_S16 idx) | false => []) | false => (match Nat.beq k 9 with | true => (stProbe 76 st_S16_9 decWList_S16 idx) | false => [])) | false => (match Nat.blt k 11 with | true => (match Nat.beq k 10 with | true => (stProbe 84 st_S16_10 decWList_S16 idx) | false => []) | false => (match Nat.blt k 12 with | true => (match Nat.beq k 11 with | true => (stProbe 84 st_S16_11 decWList_S16 idx) | false => []) | false => (match Nat.beq k 12 with | true => (stProbe 68 st_S16_12 decWList_S16 idx) | false => []))))
lemma decSt_S16_ok (s idx : Nat) : WOk (2 ^ (10 * 9) - 1) (decSt_S16 s idx) := by
  have htop : (2 ^ (10 * 9) - 1) = top_S16 := by decide +kernel
  rw [htop]; unfold decSt_S16; repeat (first | apply wOk_match | exact wOk_nil | exact decWList_S16_ok _ _)
def lookup_S16 (k : Nat) (zs : List W) : Nat := (match Nat.blt k 10 with | true => (match Nat.blt k 9 with | true => (match Nat.beq k 8 with | true => (htProbe 1 38 1 146 8 255 7 127 htd_S16_8 hta_S16_8 zs) | false => 0) | false => (match Nat.beq k 9 with | true => (htProbe 1 80 31 305 9 511 8 255 htd_S16_9 hta_S16_9 zs) | false => 0)) | false => (match Nat.blt k 11 with | true => (match Nat.beq k 10 with | true => (htProbe 1 38 1 145 8 255 8 255 htd_S16_10 hta_S16_10 zs) | false => 0) | false => (match Nat.blt k 12 with | true => (match Nat.beq k 11 with | true => (htProbe 1 5 1 23 5 31 5 31 htd_S16_11 hta_S16_11 zs) | false => 0) | false => (match Nat.beq k 12 with | true => (htProbe 1 1 1 5 3 7 1 1 htd_S16_12 hta_S16_12 zs) | false => 0))))
def applyG_S16 (g : Nat) (zs : List W) : List W := match g with
  | 1 => mapInv fixP_S16_1 swP_S16_1 fixN_S16_1 swN_S16_1 zs
  | 2 => mapInv fixP_S16_2 swP_S16_2 fixN_S16_2 swN_S16_2 zs
  | 3 => mapInv fixP_S16_3 swP_S16_3 fixN_S16_3 swN_S16_3 zs
  | _ => zs
lemma applyG_S16_sound (g s : Nat) (zs : List W)
    (hrc : ∀ w ∈ zs.map W.toPNT, RowColConst 10 9 w.1 w.2.1)
    (hnat : NatTRestricted (2 ^ (10 * 9) - 1) s (zs.map W.toPNT)) :
    (∀ w ∈ (applyG_S16 g zs).map W.toPNT, RowColConst 10 9 w.1 w.2.1) ∧ NatTRestricted (2 ^ (10 * 9) - 1) s ((applyG_S16 g zs).map W.toPNT) := by
  rcases g with _ | _ | _ | _ | g
  · exact ⟨hrc, hnat⟩
  · exact inv_list_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) hrc hnat
  · exact inv_list_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) hrc hnat
  · exact inv_list_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) hrc hnat
  · exact ⟨hrc, hnat⟩
def certHit_S16 (k : Nat) (zs : List W) : Bool :=
  let code := lookup_S16 k zs
  match Nat.beq code 0 with | true => false | false => let c := Nat.sub code 1; let q := Nat.shiftRight c 2; match Nat.blt q (cnt_S16 k) with | false => false | true => isPermW (applyG_S16 (Nat.land c 3) zs) (decSt_S16 k q)
lemma certHit_S16_sound (s : Nat) (zs : List W)
    (hrc : ∀ w ∈ zs.map W.toPNT, RowColConst 10 9 w.1 w.2.1)
    (hnat : NatTRestricted (2 ^ (10 * 9) - 1) s (zs.map W.toPNT)) (hhit : certHit_S16 s zs = true) :
    ∃ idx < cnt_S16 s, (∀ w ∈ (decSt_S16 s idx).map W.toPNT, RowColConst 10 9 w.1 w.2.1) ∧ NatTRestricted (2 ^ (10 * 9) - 1) s ((decSt_S16 s idx).map W.toPNT) := by
  unfold certHit_S16 at hhit; dsimp only at hhit
  cases h0 : Nat.beq (lookup_S16 s zs) 0 <;> simp only [h0] at hhit
  · cases h1 : Nat.blt (Nat.shiftRight (Nat.sub (lookup_S16 s zs) 1) 2) (cnt_S16 s) <;> simp only [h1] at hhit
    · contradiction
    · have hp := isPermW_sound hhit
      have ⟨h1a, h2a⟩ := applyG_S16_sound (Nat.land (Nat.sub (lookup_S16 s zs) 1) 3) s zs hrc hnat
      exact ⟨_, by simpa [Nat.blt_eq] using h1, fun w hw => h1a w (hp.mem_iff.2 hw), natTRestricted_perm hp h2a⟩
  · contradiction
def chk_S16 (k idx : Nat) : Bool :=
  match stepExpand top_S16 9 m1_S16 m2_S16 m4_S16 m8_S16 rs_S16 rf_S16 certHit_S16 k (decSt_S16 k idx) with | true => false | false => true
lemma c_S16_8_0 : span (chk_S16 8) 24 0 = true := by decide +kernel
lemma all_S16_8 : ∀ i, 0 ≤ i → i < 24 → chk_S16 8 i = true := sr rfl c_S16_8_0
lemma c_S16_9_0 : span (chk_S16 9) 16 0 = true := by decide +kernel
lemma c_S16_9_1 : span (chk_S16 9) 16 16 = true := by decide +kernel
lemma c_S16_9_2 : span (chk_S16 9) 16 32 = true := by decide +kernel
lemma c_S16_9_3 : span (chk_S16 9) 13 48 = true := by decide +kernel
lemma all_S16_9 : ∀ i, 0 ≤ i → i < 61 → chk_S16 9 i = true := rj (rj (rj (sr rfl c_S16_9_0) (sr rfl c_S16_9_1)) (sr rfl c_S16_9_2)) (sr rfl c_S16_9_3)
lemma c_S16_10_0 : span (chk_S16 10) 8 0 = true := by decide +kernel
lemma c_S16_10_1 : span (chk_S16 10) 8 8 = true := by decide +kernel
lemma c_S16_10_2 : span (chk_S16 10) 8 16 = true := by decide +kernel
lemma c_S16_10_3 : span (chk_S16 10) 8 24 = true := by decide +kernel
lemma c_S16_10_4 : span (chk_S16 10) 5 32 = true := by decide +kernel
lemma all_S16_10 : ∀ i, 0 ≤ i → i < 37 → chk_S16 10 i = true := rj (rj (rj (rj (sr rfl c_S16_10_0) (sr rfl c_S16_10_1)) (sr rfl c_S16_10_2)) (sr rfl c_S16_10_3)) (sr rfl c_S16_10_4)
lemma c_S16_11_0 : span (chk_S16 11) 8 0 = true := by decide +kernel
lemma all_S16_11 : ∀ i, 0 ≤ i → i < 8 → chk_S16 11 i = true := sr rfl c_S16_11_0
lemma c_S16_12_0 : span (chk_S16 12) 1 0 = true := by decide +kernel
lemma all_S16_12 : ∀ i, 0 ≤ i → i < 1 → chk_S16 12 i = true := sr rfl c_S16_12_0
lemma hcheck_S16 : ∀ s ≤ 12, ∀ idx < cnt_S16 s,
    stepExpand (2 ^ (10 * 9) - 1) 9 m1_S16 m2_S16 m4_S16 m8_S16 rs_S16 rf_S16 certHit_S16 s (decSt_S16 s idx) = false := by
  have htop : (2 ^ (10 * 9) - 1) = top_S16 := by decide +kernel
  rw [htop]
  have hfail : ∀ k idx, (∀ i, 0 ≤ i → i < cnt_S16 k → chk_S16 k i = true) → idx < cnt_S16 k →
      stepExpand top_S16 9 m1_S16 m2_S16 m4_S16 m8_S16 rs_S16 rf_S16 certHit_S16 k (decSt_S16 k idx) = false := by
    intro k idx hall hi; have h1 := hall idx (Nat.zero_le _) hi; unfold chk_S16 at h1
    cases hse : stepExpand top_S16 9 m1_S16 m2_S16 m4_S16 m8_S16 rs_S16 rf_S16 certHit_S16 k (decSt_S16 k idx) <;> simp only [hse] at h1
    · rfl
    · contradiction
  intro s hs idx hidx; interval_cases s
  · have h0 : cnt_S16 0 = 0 := rfl; omega
  · have h0 : cnt_S16 1 = 0 := rfl; omega
  · have h0 : cnt_S16 2 = 0 := rfl; omega
  · have h0 : cnt_S16 3 = 0 := rfl; omega
  · have h0 : cnt_S16 4 = 0 := rfl; omega
  · have h0 : cnt_S16 5 = 0 := rfl; omega
  · have h0 : cnt_S16 6 = 0 := rfl; omega
  · have h0 : cnt_S16 7 = 0 := rfl; omega
  · exact hfail 8 idx all_S16_8 hidx
  · exact hfail 9 idx all_S16_9 hidx
  · exact hfail 10 idx all_S16_10 hidx
  · exact hfail 11 idx all_S16_11 hidx
  · exact hfail 12 idx all_S16_12 hidx
lemma r_S16_0 : searchCert top_S16 9 m1_S16 m2_S16 m4_S16 m8_S16 rs_S16 rf_S16 certHit_S16 12 (mkLitWt top_S16 litW_S16 [0, 0, 2, 0, 2, 2, 2, 0] false) = false := by decide +kernel
lemma r_S16_1 : searchCert top_S16 9 m1_S16 m2_S16 m4_S16 m8_S16 rs_S16 rf_S16 certHit_S16 12 (mkLitWt top_S16 litW_S16 [0, 0, 2, 0, 2, 2, 2, 0] true) = false := by decide +kernel
lemma no_S16 : ¬ HasMono pos_S16 neg_S16 (initOf vs_S16 true) 12 := by
  have htop : 2 ^ (pos_S16.length * neg_S16.length) - 1 = top_S16 := by decide +kernel
  have hms : checkMasks pos_S16.length neg_S16.length m1_S16 m2_S16 m4_S16 m8_S16 rs_S16 = true := by decide +kernel
  intro h
  obtain ⟨k1, hk1, hm1⟩ := hasMono_to_monoLive (by decide) (by decide) 12 _ h
  obtain ⟨k2, hk2, U, hUW, hUnd, hSU⟩ := monoLive_to_sMonoLive k1 _ hm1
  obtain ⟨hperm, hlen⟩ := classify_U_w9 (by decide) (by decide +kernel) hUW hUnd hSU
  have hk_min : 12 ≤ k2 := by
    by_contra hlt
    have hv : varF 2 ∈ U := by rcases hperm with hp | hp <;> exact hp.mem_iff.2 (by simp [vs_S16])
    have ⟨_, hhm⟩ := one_zero_wire_save_one sub_S16_2.1 k2 U (fun u hu => initOf_mono _ _ u (hUW u hu)) hSU _ hv (by funext x; simp [projV, varF])
    exact sub_S16_2.2 U hUW (hasMono_mono_k (by omega) hhm)
  have hk_le : k2 ≤ 12 := by omega
  have hSub0 : ∀ u ∈ vs_S16.map varF, u ∈ initOf vs_S16 true := fun u hu => by simp [initOf, hu]
  have hk_eq : k2 = 12 := by omega
  subst hk_eq
  rcases hperm with hperm | hperm
  ·
    refine close_ht_case (vs := vs_S16) (tgs := [0, 0, 2, 0, 2, 2, 2, 0]) (withW9 := false) (cap := 12) (by decide) (by decide) (by decide) htop hms (by decide) (by decide) encLit_S16 decSt_S16_ok certHit_S16_sound hcheck_S16 (by omega) ?_ (sMonoLive_perm hperm hSU) r_S16_0
    intro wt hwt; simp only [mkWt, vs_S16, List.zipWith_cons_cons, List.zipWith_nil_left, List.append_nil, List.mem_cons, List.not_mem_nil, or_false, ite_false, Bool.false_eq_true] at hwt; rcases hwt with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · trivial
    · trivial
    · exact tagOk_of_sub sub_S16_2 hSub0 (Or.inr ⟨rfl, by omega⟩)
    · trivial
    · exact tagOk_of_sub sub_S16_4 hSub0 (Or.inr ⟨rfl, by omega⟩)
    · exact tagOk_of_sub sub_S16_5 hSub0 (Or.inr ⟨rfl, by omega⟩)
    · exact tagOk_of_sub sub_S16_6 hSub0 (Or.inr ⟨rfl, by omega⟩)
    · trivial
  ·
    refine close_ht_case (vs := vs_S16) (tgs := [0, 0, 2, 0, 2, 2, 2, 0]) (withW9 := true) (cap := 12) (by decide) (by decide) (by decide) htop hms (by decide) (by decide) encLit_S16 decSt_S16_ok certHit_S16_sound hcheck_S16 (by omega) ?_ (sMonoLive_perm hperm hSU) r_S16_1
    intro wt hwt; simp only [mkWt, vs_S16, List.zipWith_cons_cons, List.zipWith_nil_left, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false, ite_true] at hwt; rcases hwt with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · trivial
    · trivial
    · exact tagOk_of_sub sub_S16_2 (fun _ h => h) (Or.inr ⟨rfl, by omega⟩)
    · trivial
    · exact tagOk_of_sub sub_S16_4 (fun _ h => h) (Or.inr ⟨rfl, by omega⟩)
    · exact tagOk_of_sub sub_S16_5 (fun _ h => h) (Or.inr ⟨rfl, by omega⟩)
    · exact tagOk_of_sub sub_S16_6 (fun _ h => h) (Or.inr ⟨rfl, by omega⟩)
    · trivial
    · trivial

-- S0 (V=9, P=12, N=12, w9=1, k=14)
def pos_S0 : List Nat := [3, 6, 12, 17, 24, 33, 66, 132, 160, 264, 288, 320]
def neg_S0 : List Nat := [42, 50, 69, 104, 116, 138, 201, 208, 261, 276, 385, 402]
def vs_S0 : List (Fin 9) := [0, 1, 2, 3, 4, 5, 6, 7, 8]
def top_S0 : Nat := 0xffffffffffffffffffffffffffffffffffff
def m1_S0 : Nat := 0x7ff7ff7ff7ff7ff7ff7ff7ff7ff7ff7ff7ff
def m2_S0 : Nat := 0x3ff3ff3ff3ff3ff3ff3ff3ff3ff3ff3ff3ff
def m4_S0 : Nat := 0xff0ff0ff0ff0ff0ff0ff0ff0ff0ff0ff0ff
def m8_S0 : Nat := 0xf00f00f00f00f00f00f00f00f00f00f00f
def rs_S0 : Nat := 0x1001001001001001001001001001001001
def rf_S0 : Nat := 4095
def litW_S0 : List (Nat × Nat) := [(0xfff000fff000000fff, 0x544544544544544544544544544544544544), (0xfff000000000000ffffff, 0x823823823823823823823823823823823823), (0xfff000000000000ffffff000, 0x314314314314314314314314314314314314), (0xfff000000000000fff000fff000000, 0x69069069069069069069069069069069069), (0xffffff000000000, 0xa92a92a92a92a92a92a92a92a92a92a92a92), (0xfff000fff000000fff000000000000000, 0x1b01b01b01b01b01b01b01b01b01b01b01b), (0xfff000000000000fff000000000000000000, 0xdc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc), (0xffffff000000000000000000000, 0xce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0), (0xfffffffff000000000000000000000000000, 0xf00f00f00f00f00f00f00f00f00f00f00f00), (0xffffff000fff000ffffff, 0xd67d67d67d67d67d67d67d67d67d67d67d67)]
lemma encLit_S0 : (initOf vs_S0 true).map (fun f => (encPos pos_S0 neg_S0.length f, encNeg pos_S0.length neg_S0 f)) = litW_S0 := by decide +kernel
def pi_S0_0 : Fin 9 → Fin 9 := fun i : Fin 9 => (match i.1 with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8 : Fin 9)
lemma sub_S0_0 : SubJust pos_S0 neg_S0 (initOf vs_S0 true) pos_S1 neg_S1 0 pi_S0_0 11 :=
  mkSubJust 0 pi_S0_0 (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) no_S1
def pi_S0_1 : Fin 9 → Fin 9 := fun i : Fin 9 => (match i.1 with | 0 => 1 | 1 => 0 | 2 => 5 | 3 => 8 | 4 => 6 | 5 => 2 | 6 => 4 | 7 => 7 | _ => 3 : Fin 9)
lemma sub_S0_1 : SubJust pos_S0 neg_S0 (initOf vs_S0 true) pos_S1 neg_S1 1 pi_S0_1 11 :=
  mkSubJust 1 pi_S0_1 (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) no_S1
def pi_S0_2 : Fin 9 → Fin 9 := fun i : Fin 9 => (match i.1 with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8 : Fin 9)
lemma sub_S0_2 : SubJust pos_S0 neg_S0 (initOf vs_S0 true) pos_S5 neg_S5 2 pi_S0_2 11 :=
  mkSubJust 2 pi_S0_2 (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) no_S5
def pi_S0_3 : Fin 9 → Fin 9 := fun i : Fin 9 => (match i.1 with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8 : Fin 9)
lemma sub_S0_3 : SubJust pos_S0 neg_S0 (initOf vs_S0 true) pos_S11 neg_S11 3 pi_S0_3 11 :=
  mkSubJust 3 pi_S0_3 (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) no_S11
def pi_S0_4 : Fin 9 → Fin 9 := fun i : Fin 9 => (match i.1 with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8 : Fin 9)
lemma sub_S0_4 : SubJust pos_S0 neg_S0 (initOf vs_S0 true) pos_S14 neg_S14 4 pi_S0_4 12 :=
  mkSubJust 4 pi_S0_4 (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) no_S14
def pi_S0_5 : Fin 9 → Fin 9 := fun i : Fin 9 => (match i.1 with | 0 => 1 | 1 => 0 | 2 => 5 | 3 => 8 | 4 => 6 | 5 => 2 | 6 => 4 | 7 => 7 | _ => 3 : Fin 9)
lemma sub_S0_5 : SubJust pos_S0 neg_S0 (initOf vs_S0 true) pos_S5 neg_S5 5 pi_S0_5 11 :=
  mkSubJust 5 pi_S0_5 (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) no_S5
def pi_S0_6 : Fin 9 → Fin 9 := fun i : Fin 9 => (match i.1 with | 0 => 1 | 1 => 0 | 2 => 5 | 3 => 8 | 4 => 6 | 5 => 2 | 6 => 4 | 7 => 7 | _ => 3 : Fin 9)
lemma sub_S0_6 : SubJust pos_S0 neg_S0 (initOf vs_S0 true) pos_S14 neg_S14 6 pi_S0_6 12 :=
  mkSubJust 6 pi_S0_6 (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) no_S14
def pi_S0_7 : Fin 9 → Fin 9 := fun i : Fin 9 => (match i.1 with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8 : Fin 9)
lemma sub_S0_7 : SubJust pos_S0 neg_S0 (initOf vs_S0 true) pos_S16 neg_S16 7 pi_S0_7 12 :=
  mkSubJust 7 pi_S0_7 (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) no_S16
def pi_S0_8 : Fin 9 → Fin 9 := fun i : Fin 9 => (match i.1 with | 0 => 1 | 1 => 0 | 2 => 5 | 3 => 7 | 4 => 2 | 5 => 6 | 6 => 4 | 7 => 8 | _ => 3 : Fin 9)
lemma sub_S0_8 : SubJust pos_S0 neg_S0 (initOf vs_S0 true) pos_S11 neg_S11 8 pi_S0_8 11 :=
  mkSubJust 8 pi_S0_8 (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) no_S11
def wp_S0 (i : Nat) : Nat := (bn (Nat.blt i 5) (bn (Nat.blt i 2) (bn (Nat.blt i 1) 0xfff000ffffff000fff000000ffffff000000000000000fff000fff000000fffffffff000000000000000fff000000000000ffffff000fff000000000000fff000fff000000fff000fff000000000fff000000000000ffffff000000000000000ffffff000000000fffffffff000000000000fff000000000000000000fffffffff000000fff000000000000fffffffffffffff000000000000000000000000000000000000ffffff000000000000000000000000000000000000000000ffffff000000000000000000000000000fff000fff000000fff000000000000fff000000000000ffffff000fff000000000000ffffff000000000ffffff000000fff000000000000fff000fff000000000fff000fff000000fff000000000000000 0xfffffffff000fff000000000000ffffff000000fffffffff000fffffffff000fffffffff000ffffff000fff000000000000ffffff000fffffffff000000fff000000000fff000000fffffffff000fff000fff000ffffffffffff000fff000fff000ffffff000000000fffffffffffffff000000000000000000ffffff000000000fffffffff000000000000ffffff000000000000000000000fff000ffffff000ffffff000000000000fff000000000ffffffffffffffffff000000000fff000000000000000000000fff000000000000fff000fffffffff000000000000000000fff000fff000ffffff000000fff000000000ffffffffffff000fff000000000000000000fff000ffffffffffff000000000ffffff000000000000fffffffff) (bn (Nat.blt i 3) 0xfff000fff000ffffffffffffffffff000000000000000000000000000fffffffff000fff000ffffff000fff000000fffffffff000000000000000ffffff000fff000ffffff000000fff000000000fff000fff000000ffffffffffff000000ffffff000000000ffffff000000000000ffffff000000000fffffffff000000000000fff000fff000ffffffffffff000000fff000000000ffffffffffffffffff000fff000000000ffffff000000000ffffff000000000000000000fffffffff000fffffffffffffff000000000000000000000fff000000000fff000000fff000fff000fffffffff000000fff000000fff000000000fffffffff000000fff000000000000ffffffffffff000fffffffff000000000000000000000ffffff (bn (Nat.blt i 4) 0xfffffffff000000ffffff000fff000000000000fff000000ffffff000fff000ffffff000fff000fff000000fff000000fff000000fffffffff000000000000fff000fff000000000ffffff000000fff000000000fffffffff000000000000000ffffff000ffffffffffff000fff000ffffffffffff000000fffffffff000000fff000000000000fff000fff000fff000000000000000000fff000000000ffffff000000000000fff000000000000fffffffff000000fff000ffffffffffffffffffffffff000000000000000000fff000fff000fffffffffffffff000000ffffff000fff000ffffff000000fff000000fffffffffffffffffffff000000000000000ffffff000000000ffffff000000000000fffffffff000ffffffffffff 0xfff000fff000000000000ffffff000fffffffffffffffffffff000ffffffffffff000000000000000000fff000fff000ffffff000fff000fff000000fff000fff000000fff000000000000000000fff000fff000000fff000fff000fff000000fff000fff000ffffff000000000000000000fff000000000000000fffffffff000ffffff000000000ffffffffffffffffffffffffffffff000000fffffffff000000000000000000fff000000fff000000fffffffff000fffffffff000fffffffffffffffffffff000fffffffff000000fffffffffffffffffffffffffffffffffffffffffffff000fffffffff000000ffffff000ffffff000fffffffff000000000fff000000000000000000000000000fff000fff000000ffffff000))) (bn (Nat.blt i 8) (bn (Nat.blt i 6) 0xffffffffffff000ffffff000ffffff000000fff000fff000000fff000000000fff000000ffffff000000000000fffffffff000000000ffffff000000000000000000fff000000fffffffff000fffffffffffffffffffffffffffffffff000000fff000fff000ffffffffffffffffffffffff000fff000fffffffffffffffffffffffffff000ffffff000ffffff000fffffffff000000fffffffffffffffffffff000000fff000000fff000000000000ffffff000000fff000000000000fff000ffffff000fffffffff000000000000000000000000ffffffffffff000000000fff000fff000000ffffffffffff000fff000000fff000ffffff000fffffffff000000000000000000fff000000000000fff000fff000000fff000ffffff000 (bn (Nat.blt i 7) 0xfff000fff000ffffff000fff000fffffffffffffff000000000ffffffffffff000fff000000000000000000fff000000000ffffff000fff000fff000000fff000fff000ffffff000000000000000000fff000fff000fffffffffffffff000ffffff000fff000ffffffffffffffffff000000000fff000fff000ffffff000000fff000000000000000000ffffff000fffffffff000fff000ffffffffffffffffff000fff000ffffffffffff000ffffffffffff000000000000000fff000000000fffffffff000000000000fff000fff000000ffffff000000000000000fffffffff000000fffffffff000fff000000fff000000000000ffffff000ffffffffffffffffffffffff000fffffffff000ffffff000000000000fff000fff000000 0xfffffffff000000ffffff000000000ffffff000fff000ffffff000fff000ffffffffffff000000000000000000fff000000000fff000fffffffffffffff000fff000000ffffff000000000000000000000fff000fff000000fff000000000000000000fff000fff000000ffffffffffff000000000fff000fff000ffffff000000000000000fff000000000000ffffff000000000000000fff000000000000ffffff000000fff000fff000ffffff000ffffff000fffffffff000000000ffffffffffffffffffffffffffffff000ffffff000fff000ffffffffffffffffff000ffffff000000000ffffffffffffffffff000000fff000fff000ffffff000000000000000000000000000000fff000ffffffffffff000000fff000000000000000)) (bn (Nat.blt i 9) 0xfff000000000000000000000000000000000ffffff000000fff000ffffff000fff000fffffffff000000fff000000fff000000000000ffffff000000fff000000fff000000000000ffffff000000000000000ffffff000000000ffffff000000000000fffffffff000000fffffffffffffffffffff000000fff000fff000000fff000000000000000fff000000000000ffffff000000000000000fff000000000000ffffff000000000000000000000000000000fff000000000fff000000000ffffffffffffffffff000000000000000000fff000fff000000ffffffffffff000000000fff000fff000ffffff000000000000000000000000000000fff000000000000000000000fff000fff000ffffff (bn (Nat.blt i 10) 0xfff000000000000000fffffffff000000000fff000000000fff000000fff000000000000fff000000000fff000000000000000000fff000000000fffffffff000000000000000000fff000ffffff000fff000000000000000000000000000fff000000000000fff000000000000000000000fff000000000000000000000000000000ffffff000000000fff000000000000000000fff000000ffffffffffff000000ffffff000fff000000000000fff000000000000000000000000fff000000000000000000fff000000000fff000000000000000000000fff000000000000000000000fff000000000000000000ffffff000000fff000000000000000000000000fff000000000000000000000000000000000fff000 0xfff000000000fffffffff))))
def wn_S0 (i : Nat) : Nat := (bn (Nat.blt i 5) (bn (Nat.blt i 2) (bn (Nat.blt i 1) 0x31f31f31f31f31f31f31f31f31f31f31f31f3143143143143143143143143143143143148238238238238238238238238238238238235445445445445445445445445445445445448238238238238238238238238238238238238238238238238238238238238238238238230dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dcf23f23f23f23f23f23f23f23f23f23f23f23f00f00f00f00f00f00f00f00f00f00f00f00ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0a92a92a92a92a92a92a92a92a92a92a92a925445445445445445445445445445445445443143143143143143143143143143143143140dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc06906906906906906906906906906906906901b01b01b01b01b01b01b01b01b01b01b01b 0xf14f14f14f14f14f14f14f14f14f14f14f1487b87b87b87b87b87b87b87b87b87b87b87b3143143143143143143143143143143143140dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dcf54f54f54f54f54f54f54f54f54f54f54f5483b83b83b83b83b83b83b83b83b83b83b83bf00f00f00f00f00f00f00f00f00f00f00f00ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce05445445445445445445445445445445445440dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dcf00f00f00f00f00f00f00f00f00f00f00f0006906906906906906906906906906906906954454454454454454454454454454454454456d56d56d56d56d56d56d56d56d56d56d56d544544544544544544544544544544544544ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0) (bn (Nat.blt i 3) 0x77d77d77d77d77d77d77d77d77d77d77d77d04004004004004004004004004004004004031f31f31f31f31f31f31f31f31f31f31f31fd67d67d67d67d67d67d67d67d67d67d67d67544544544544544544544544544544544544f23f23f23f23f23f23f23f23f23f23f23f23b37b37b37b37b37b37b37b37b37b37b37b3775475475475475475475475475475475475456d56d56d56d56d56d56d56d56d56d56d56d823823823823823823823823823823823823a92a92a92a92a92a92a92a92a92a92a92a92f00f00f00f00f00f00f00f00f00f00f00f0086b86b86b86b86b86b86b86b86b86b86b86b823823823823823823823823823823823823a92a92a92a92a92a92a92a92a92a92a92a92f00f00f00f00f00f00f00f00f00f00f00f00 (bn (Nat.blt i 4) 0x7b07b07b07b07b07b07b07b07b07b07b07bd67d67d67d67d67d67d67d67d67d67d67d6701b01b01b01b01b01b01b01b01b01b01b01bf69f69f69f69f69f69f69f69f69f69f69f69833833833833833833833833833833833833d67d67d67d67d67d67d67d67d67d67d67d67b3fb3fb3fb3fb3fb3fb3fb3fb3fb3fb3fb3f069069069069069069069069069069069069010010010010010010010010010010010010314314314314314314314314314314314314f7ff7ff7ff7ff7ff7ff7ff7ff7ff7ff7ff7f744744744744744744744744744744744744f67f67f67f67f67f67f67f67f67f67f67f67d6fd6fd6fd6fd6fd6fd6fd6fd6fd6fd6fd6f833833833833833833833833833833833833f77f77f77f77f77f77f77f77f77f77f77f77 0x314314314314314314314314314314314314f7ff7ff7ff7ff7ff7ff7ff7ff7ff7ff7ff7fd44d44d44d44d44d44d44d44d44d44d44d4455f55f55f55f55f55f55f55f55f55f55f55f547547547547547547547547547547547547d5fd5fd5fd5fd5fd5fd5fd5fd5fd5fd5fd5f040040040040040040040040040040040040f37f37f37f37f37f37f37f37f37f37f37f37f3ff3ff3ff3ff3ff3ff3ff3ff3ff3ff3ff3f050050050050050050050050050050050050f77f77f77f77f77f77f77f77f77f77f77f77f37f37f37f37f37f37f37f37f37f37f37f37f7ff7ff7ff7ff7ff7ff7ff7ff7ff7ff7ff7fd7fd7fd7fd7fd7fd7fd7fd7fd7fd7fd7fd7ff63f63f63f63f63f63f63f63f63f63f63f63377377377377377377377377377377377377))) (bn (Nat.blt i 8) (bn (Nat.blt i 6) 0x37f37f37f37f37f37f37f37f37f37f37f37f01b01b01b01b01b01b01b01b01b01b01b01ba92a92a92a92a92a92a92a92a92a92a92a92010010010010010010010010010010010010f7ff7ff7ff7ff7ff7ff7ff7ff7ff7ff7ff7ff6bf6bf6bf6bf6bf6bf6bf6bf6bf6bf6bf6bf5ff5ff5ff5ff5ff5ff5ff5ff5ff5ff5ff5ff7ff7ff7ff7ff7ff7ff7ff7ff7ff7ff7ff7ff6ff6ff6ff6ff6ff6ff6ff6ff6ff6ff6ff6f823823823823823823823823823823823823069069069069069069069069069069069069f00f00f00f00f00f00f00f00f00f00f00f00f44f44f44f44f44f44f44f44f44f44f44f44f7df7df7df7df7df7df7df7df7df7df7df7df00f00f00f00f00f00f00f00f00f00f00f0037d37d37d37d37d37d37d37d37d37d37d37d (bn (Nat.blt i 7) 0xd7fd7fd7fd7fd7fd7fd7fd7fd7fd7fd7fd7ff6df6df6df6df6df6df6df6df6df6df6df6d00000000000000000000000000000000000055f55f55f55f55f55f55f55f55f55f55f55f565565565565565565565565565565565565f7ff7ff7ff7ff7ff7ff7ff7ff7ff7ff7ff7ff44f44f44f44f44f44f44f44f44f44f44f44800800800800800800800800800800800800f7df7df7df7df7df7df7df7df7df7df7df7df7ff7ff7ff7ff7ff7ff7ff7ff7ff7ff7ff7f823823823823823823823823823823823823314314314314314314314314314314314314b37b37b37b37b37b37b37b37b37b37b37b37314314314314314314314314314314314314f7ff7ff7ff7ff7ff7ff7ff7ff7ff7ff7ff7f069069069069069069069069069069069069 0xf27f27f27f27f27f27f27f27f27f27f27f2775f75f75f75f75f75f75f75f75f75f75f75fd07d07d07d07d07d07d07d07d07d07d07d07f1ff1ff1ff1ff1ff1ff1ff1ff1ff1ff1ff1f744744744744744744744744744744744744d44d44d44d44d44d44d44d44d44d44d44d44f65f65f65f65f65f65f65f65f65f65f65f65d23d23d23d23d23d23d23d23d23d23d23d23863863863863863863863863863863863863f7ff7ff7ff7ff7ff7ff7ff7ff7ff7ff7ff7ff6df6df6df6df6df6df6df6df6df6df6df6df7ff7ff7ff7ff7ff7ff7ff7ff7ff7ff7ff7ff3bf3bf3bf3bf3bf3bf3bf3bf3bf3bf3bf3bf5ff5ff5ff5ff5ff5ff5ff5ff5ff5ff5ff5f021021021021021021021021021021021021f1bf1bf1bf1bf1bf1bf1bf1bf1bf1bf1bf1b)) (bn (Nat.blt i 9) 0x165165165165165165165165165165165165700700700700700700700700700700700700b7fb7fb7fb7fb7fb7fb7fb7fb7fb7fb7fb7f863863863863863863863863863863863863d23d23d23d23d23d23d23d23d23d23d23d23927927927927927927927927927927927927f37f37f37f37f37f37f37f37f37f37f37f37f5ff5ff5ff5ff5ff5ff5ff5ff5ff5ff5ff5f833833833833833833833833833833833833927927927927927927927927927927927927800800800800800800800800800800800800d6dd6dd6dd6dd6dd6dd6dd6dd6dd6dd6dd6d565565565565565565565565565565565565f47f47f47f47f47f47f47f47f47f47f47f47003003003003003003003003003003003003547547547547547547547547547547547547 (bn (Nat.blt i 10) 0xd03d03d03d03d03d03d03d03d03d03d03d03f07f07f07f07f07f07f07f07f07f07f07f07307307307307307307307307307307307307863863863863863863863863863863863863565565565565565565565565565565565565f61f61f61f61f61f61f61f61f61f61f61f6136536536536536536536536536536536536500b00b00b00b00b00b00b00b00b00b00b00b504504504504504504504504504504504504f7bf7bf7bf7bf7bf7bf7bf7bf7bf7bf7bf7b840840840840840840840840840840840840107107107107107107107107107107107107063063063063063063063063063063063063d04d04d04d04d04d04d04d04d04d04d04d04d14d14d14d14d14d14d14d14d14d14d14d14d04d04d04d04d04d04d04d04d04d04d04d04 0x927927927927927927927927927927927927))))
def fixP_S0_1 : Nat := 0xfff000000000000000000000000fff
def swP_S0_1 : List (Nat × Nat) := [(0xfff000000000000000000000, 12), (0xfff000000000, 36), (0xfff000, 48), (0xfff000000000000, 84), (0xfff000000, 96)]
def fixN_S0_1 : Nat := 0x90090090090090090090090090090090090
def swN_S0_1 : List (Nat × Nat) := [(0x2002002002002002002002002002002002, 1), (0x60060060060060060060060060060060060, 5), (0x8008008008008008008008008008008008, 6), (0x1001001001001001001001001001001001, 8)]
def st_S0_9 (i : Nat) : Nat := (bn (Nat.blt i 1) 0x741a250361300e0980500a41d068940a012038260140291501a058351300e0980500a41d068160d84c038261400190781a058351300e09806006490068160d811038260140291b02006816230480382600641e06816220480480e0980190781a210361201203826006480068160d812038260140190807c068161e0110f02601a420068160d8111d0260180290801a058360440e1c00600a46c0801a058680483c0980591901a058360443c0980600a41e180160d8110f0260180290741a058361100e0980600641e068160d45c038260180190801e068160480e098500064200781a05812038580180190781a058361300e09805006454068160d412038260140290741a058360480e0985000641d068160d84c038260180190741a05836120380980600a41d068160d8440f02601802907440058360483c0980600a41d068160d8120e0260140290781a058350c00e0980500a41e068160b011038260140290741a058280480e0980500a4200781a0581203808014029 0x781a058340440e0980600641e068160d41003826018019078b006816260a00f02601641d2c01a250682803c098059074b0068161a0a02d02601641d2c01a058682803c0980590781a05898280120f02601641d068160d84c0e0260140290741a058351103c0980600a41e068160a011038260140290781a058340440e0980500a41e068160d4ac038260180192a07c068161a0110f02601641e068160d410038260140292401a058280440e0980500a41e068160d444038260180190741a058351100e09806006480068160d84c038260140190741a29016230a02702600641e068160d44c038260140290741a05828048380980500a41e068162601103826014029)
def htd_S0_9 (_ : Nat) : Nat := 0x8000000000000000000000200000000000000000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000000000000010000000000000002000000000000000200000000000
def hta_S0_9 (i : Nat) : Nat := (bn (Nat.blt i 2) (bn (Nat.blt i 1) 0x50000000000010000000000000000001b0000000000000000008c0430000000014e8007a0000000000000000000012c0000000000000000068000660000008002800000000000000000007d98000000000110000000000000000000001bdf00000000003400000000000000800000000 0x1da500000000000000000000000000001aac0000003380000000000000003a0000000000000002b80000000000000000084000000ca55000328000007800000000016c0027800000000188000240000000000000006a529c0000180000017400000000000000000) (bn (Nat.blt i 3) 0x6a2c0115800bcd0a0000001270800000000000000000000000000000000228000000078200000004c069c600000000000000000009e7a3592ce4200360000000000000000000000002f000000000029000000000320000000023800001358000288001500400055c6b00000000000000 0xb4000000005e))
def st_S0_10 (i : Nat) : Nat := (bn (Nat.blt i 4) (bn (Nat.blt i 2) (bn (Nat.blt i 1) 0x3c07c2c01a058350443c098fca078f8068160d8120342601801a074e8068160d8120382601801a0807c2c01a058680443c09805a1f01e068161a0280443c09805a1b01e2c01a058680483c09805a074b0068160d4a00f026018f4a3c07c2c01a058680443c09806a078b0068163b0110382601802a0741a058360483809805008dca074b0068161a04c0382601402a0801e068160480e09805008dca074e8068160d8a00382601801a074b0068e4058682802601402a0801e06816230a01200e09801a0741a05836280480382638001a0741a0588c0d8481700e09801a0741a250360480e09805008dca3001d068160d8123602601401a3501d068160d8120382601801a078b0068160d8d00382601401a3301e068160d84c0382601401a074b0068160d8440382601801a074c8068160d84c0382601801a074b006816310120382601402a3001d068160a0120382601402a0741a0588c0d89c0480e09801a0801e06816230bc0480e09801a07440058360480e098062e001a0741a058361100e098062e001a0741a058360480e160062e001a0741a058360480e098502e001a 0x815006816230120342601801a5302006816560120342601801a33150068160d8120342601401a0781a0588c560115000e09801a5302006816230125000e09801a0801e06816230110382655001a53150068160d8480342601801a53020068160d8ac0342601801a1b01e068160a0120382601402a5201e068160a0110382601802a510b0068161a0110382601802a3c07c068160a0110382601802a1f01e068160a0115002601802a078b0068161a0114f02601802a4e01e068160d4120382601402a07934068160d5300382601402a1b01e068160d52c0382601402a074b0068a4058782802601802a07928068160d4120382601402a4401e068160d8110382601402a0741a058350480e0980649002a4801e068160a0110382601402a4701e068160a0110382601402a0741a058351300e0980646002a4501e068160a0110382601402a4401e068160a0110382601402a0807c068160a0110382601402a4301e068160d4110382601802a07908068160d4110382601802a4107c068160d4110382601802a1f01e068160d4114002601802a078b0068160d4111d02601802a) (bn (Nat.blt i 3) 0x1b01e068160d4480f02601802a000201f01a058680443c0980590781a05835044740980600970a1f01e2c01a058680483c09805a0741a05835280120f026018f4a1f01e068160d8110f02601578a3c07c068161a0360443c09806a0781a5d0350440e0980600970a1b01e068161a0360483c09805a1b01e06816230361200e09801a1f090068160d8115002601801a0807c068160d8114f02601801a0809006816230110382601801a0807c06816560110382601801a1b02006816230120382601801a0807c06816230480480e09801a5b01e068160d8120382601801a1b020068160d8480382601801a4801e06816230480480e09801a08090068161a0110382601402a0807c068160b0110382601402a1b020068161a0120382601402a0807c068161a0115002601802a5a07c06816230360454009801a4807c0781a0588c0454009801a000201f01a0588c045400980190781a0588c0d8115013c09801a1f01e068160d8115002655001a4701e068160d8110382601402a5901e068160d4120382601402a5801e068160d4110382601802a5701e068160d8120342601801a 0x74c8068a40588c2802601801a0741a29016230bc2801209801a0741a05836280483602601801a0741a290160d8a01702601801a0741a0588c650480480e09801a0741a29016230120382638001a5301e068a40588c1200e09801a0001d068a40588c280480980190001d068160d8120e026014029074b0068160d8a06402601402a0741a630160d8a00482601402a0741a058362804c0f02601402a0807c068160d8116202601402a1f144068160d4110f02601802a3c07c068160d4116202601802a4e01e068160d8120382601402a0741a290160d8a0120263f002a1f090068160d8110f02601402a1b020068160d8120f02601402a6101e068160d8110382601802a3c07c068160d4110382660002a0801a058360440e0980600970a0807c068161e0110382601802a0807c068160d8115f02601802a0001e068160d4111d0260180291b01e068160d4120f0263f006a1f01e068160d4110f026018f4a000f01f01a058350443c098fc90807c068160d8110f0263f006a3c07c068160d4115f0263f002a5a07c068160d8110f02601802a0807c06816230110f02601802a)) (bn (Nat.blt i 6) (bn (Nat.blt i 5) 0x1b020068160d84c0382601401a1b01e068160d44c0382601401a1b01e068160d49c0382601801a0741a058360480e09805009b4a3301e068160d44c0382601401a074c8068160d44c0382601801a6901e068160d49c0382601801a6901e068160d5b00382601402a4501e068160d84c0382601401a4501e068160d44c0382601401a07934068160d4a00382601401a078b0068160d4d00382601401a0741a05835281ac0382601801a4501e068160d8120382601401a0741a29016650a00482601801a6a01e068160d8110382601801a074c8068160d8a00f02601802a0741a058352805c0f02601802a0741a390160d8a01202601802a0741a05835280486402601802a0741a0588c0d8a01203c09802a0001d2c01a058682803c0980590801e068161a0a00483c09805a69020068160d8120382601401a0741a05836280120f02601578a1901a05836680110382601801a0786005836680110382601801a0781a21036680110382601801a0781a05888680110382601801a6701e068160d4120382601801a6601d068160d8120382601402a0741a29016230123602601801a 0x79e006816770110342601801a5701e068160d8110342601801a078f8068160d8110342601801a074c8068160d8110382655001a7601e068160d4110382601802a078b006816560a00382601801a074c8068160d8a00382601801a5a01e068160d84c0382601801a0801e068162304c0382601801a0741a058361300e098062e001a0741a058352f04c0382601801a7501e068160d44c0382601801a078f8068160d4a00382601801a074e8068160d4a00382601801a5701e068160d44c0382601801a7401e068160d44c0382601402a0741a058280480e09805009b4a7301e068160d84c0382601402a078b0068160b0a00382601402a0801e068161a04c0382601402a3501d068160d44c0382601801a6701e068160d44c0382601801a3501d068160d84c0382601801a0741a0588c0d8bc1300e09801a7201e068160d44c0382601402a074b0068160d8a00382638001a7201e068160d4120382601402a0741a058360440e0980671002a531c0068160d44c0382601402a075bc068160d8120382601402a6e01e068160d44c0382601801a0741a0588c0d8481300e09801a) (bn (Nat.blt i 7) 0x74b0068161a1f82803c09805a074b0068161a0a00f02601578a3c01e2c01a058682803c09806a3301e2c01a058682803c09805a1b01e2c01a058682803c09805a7c01e2c01a058682803c09805a079f4068160d4110382601402a7c01e068160d4110382601402a7301e2c01a058682803c09805a074b00698c058362802601402a0741a05835280440f02601802a074c8068e4058362802601802a074b0068161a0a01303c09805a074b0068e40588c2802601802a3301e068161a0a00483c09805a0741a058680a0a00483c09805a5301e2c01a058682803c09805a0801e2c01a058682803c09805a075bc2c01a058682803c09805a074c8068160d4a06402601802a3301e068160d8120382601401a540b0068160d8a00382601401a4501e068160d4120382601401a074c8068160d8120382601801a3501d068160d4120382601801a079e8068160d5ec0382601401a079e8068160d4bc0382601801a5301e068160d5ac0382601801a7901e068160d4120382601801a53020068160d84c0382601401a7501e068160d4120382601801a074e8068160d4120382601801a (bn (Nat.blt i 8) 0x741a390160a0a00482601402a6601d068160a0110382601402a6601d068160a0120382601402a074c8068160d8a03602601801a3501d068160d8110382601801a0741a05a18770110382601801a0741a290160d8a01102601801a074e8068160d8110382601801a5b01e068160d4110382601801a5b01e068160d8110382601801a0781a05836850110382601801a33090068160d8110382601401a4e01e068160d4110382601402a4801e06816770110382601801a4e01e068160d8110382601402a07a10068160d4120382601801a5b01e068160d4120382601801a07934068160d4480382601801a0807c2c01a0588c0454009801a1b01e068160d60c0382601801a074c8068160d4a00f02601802a1b01e068160d44c0f02601402a0741a390160d8a01302601402a0741a05835282000f02601402a8201e068160d4120382601402a0741a058360440e0980600a04a079e8068160d5f80382601402a5301e068160d6000382601402a7f01e068160d8110382601402a3001d068160d4126402601402a074b0068160d8120e02601402a6601d2c01a058682803c09805a 0x74b006816310110382601402a6601d068160d8110382601402a074b0068161a0120382601402a3001d068160a0110382601402a0741a390160a0110382601402a0741a05a281a0110382601402a0741a29016230a01302601801a074b0068a40588c2f0a009801a074c8068a4058362802601801a074b0068a40588c2804809801a8901e068160d8110382601402a8801e068160d44c0382601402a0741a05a18870110382601402a074b0068161a0123602601402a074b0068a4058282802601402a074b0068e4058682813009805a074c8068a4058682802601802a0741a290160a0a00482601402a074b0068e4058282802601402a074b0068161a0a00e02601402a5901e068160d44c0382601402a4501e068160d8110382601401a074b0068e4058782802601802a078b006816260a00382601402a3301e068161a04c0382601402a))))
def htd_S0_10 (i : Nat) : Nat := (bn (Nat.blt i 1) 0xc0000100000000000000000000000000000100000000000000002000000000000000000200000000000002000000000000000000000000000000000000000000000000000000000400000000000000040000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000401000000004008000000000080000000000000000004000000000000000000200400000 (bn (Nat.blt i 2) 0x40100000000000800000000000000000000080000000000000002000008000000000000100800000000000000000000000040000000000000001000000000000000000000100000000000002000000000000000000100200001000000004000000040100000000200000000000000000000000080000100000000000004000000000000000000000200000000000000000010000000000000400800800000000000000020000280000000000000 0x8000010000000000200000000000000000008000000000000000000000000000000000010000000000000400000800002004000000000000000000000000000000000000020000000000000000000000002004000000000000000100000000000000000000000000000000000000000000004004000000000000000000000400000000000000000000000000000400000000000008000000000000000000200000000))
def hta_S0_10 (i : Nat) : Nat := (bn (Nat.blt i 6) (bn (Nat.blt i 3) (bn (Nat.blt i 1) 0x46c00000002f800374a1000000001300000000000000000000000004740000000000007ac00000000000000000000000000000153000000000000055001ad00000528000000008c0000000000000006e000000022c1c80000000664000000000000001250000000000000000c4000000000000165cb7c0bf288276c826000e70000005c0000000000d66a4000000000000000000000000000000006700000000 (bn (Nat.blt i 2) 0x94700017b0000025c0000000000008bd8d194df41400000000000041c000000000000001d500000000ef0000024e120000000000000007dc000021b1dc002ec0000079000003609f68cf600000000006f800000000000000057001af7518100000000000000000000000008408b000000000019000000000000000000001cc000000a4000000000000000003b0000000000000004af00000000000000000000 0x2c885001f50017300000001bd000000000000083000000000000000000006a18300000534000017800000000f7000000000b0000000000000000000000000001e50000000000000000020400000001436940000000000000000052c00000008a0bc00000000000000083c52000157740000000000002e8000012f18c00000b400000000f000000000000003d1819e000000000079c00000000000000000001c5)) (bn (Nat.blt i 4) 0xb84d00000804006e1fc0015e000003f400000215b40000000000003fc000000000000001ab554001040000000000006cc0000000001a700000001595a00036c0082db7000000002d000006d00000000000000006f00000000000000000000000001ac0000000000000000067c00001e900000000002ce070014500000000000000a0000029400000000000000000000da00000460000021e00053 (bn (Nat.blt i 5) 0x6fc4500000000000000031d5b00030481e0002090000000000000ae000000000000163000e0000000000000000000000016900000000001a91187c00000000000000000000000000089c4200000000000000000043000c100000000007b5890000000000001ff3d4000000053c0000000000006e8003e400001e10ad095bd13000f46e40012c00000000006d00000000000000000000000006c000 0x16935000000000000068000005e4000013700000000007c40070400000000000000000000001edaa5ac00001fb000000000000000000000000000000001ce1a40000000001fd0000000000000050000000000000005840000000000c82611c63c000000000000000000000000000000004f40000000000c034d620007300036000003b4000000000000001cf00000000000d0000e00e001e40a9ca2814e8c800))) (bn (Nat.blt i 9) (bn (Nat.blt i 7) 0x8319b000000020d64e0300000000d1000f1000000000076800384f36c56513d9d3400061c000012900000000000010600214455e3000000021d00000000000000000000000893509668849000000000088c000000000000000000000052400000000000000000000002180000000000a30000000000000000000000000000000000000000000004e456000000000000000001750000000000000000003b75ccf (bn (Nat.blt i 8) 0x1ef8540000000000000000000000234000004e839e80003216cb50015c15000819c00000000000000000017f760000007500000000000000019c0000050000000000000000000990000069800631fe07c0000000000000009d0000056a132c4000012b0000000000001950000000000000000000055c000000000000000006d40085da4001d100000000000000000000001d9000000000016000000ab 0x204004fc000000000000000000000071c00000000002f8717d4b400000ce001b60000045c07644b6254c650400001853ec000008f65c002b5db26c00000000000000000000000000000000000001100073400000000780000000000000000000000684e500133000000000000000001bb49c0038c00000090000000000000000000000000000a777dd000000000000010d8143f000000011400000)) (bn (Nat.blt i 10) 0x314e90000051c008c40000000000000000000000000000003a0000057c0000000184000010f000000000000000000007241d0b000000000001059c4c8a8e20005f00216000000000000000680cc17800000000011900000000000000088403000000ddae0001b00000000bd0d521000000000000000000000000000000000000000000000000eb40400000000000000000000000005d00000000910000000000 (bn (Nat.blt i 11) 0xb80000000000000008ac0027000000000007d0000000000000000013b355f9000cd800cb000b00000000000001d30010b000000015d000000012370c7f47d5104400000c3000000018b002198b4878a40000000000004c4000000012000000d9000000000000000324005c400000007480000000000000900040c0000000000004400000000000007cc000000f000d711c000000000000000008283908819 0x1c4b900000000000340000000710002a4008440011a25))))
def st_S0_11 (i : Nat) : Nat := (bn (Nat.blt i 11) (bn (Nat.blt i 5) (bn (Nat.blt i 2) (bn (Nat.blt i 1) 0x1cc4801e068160d8110382601402b001a80801e068160d8110382601801b0014c0801a05836049400382601801b0019c5301e068160d4120382601801b0019c0781a05835049400382601801b000cc0781a05836049400382601801b000d4074b0068160d8120382601801b001a80781a05836045400382601801b001480781a8d0160d8110382601801b0001d3201a8d0160d8110382601801b000cc0781a0588c0d8120342601801b000000781a05a300d8110342601801a0015c0781a0588c0d8110342601801b00168078c8068160d8110342601801b000cc1b01e068160d4120382601401b001145701e068160d4110382601801b001485701e068160d4110382601801b000000801e06816770110342601801a00020078c806816230110342601801b00000078b006816560110342601801a00000079e006816230110342601801a000cc0801e06816230110342601801b0014c080c8068160d8120342601801b0000007a2c068160d8110342601801a00000540b0068160d8120342601401a000cc4801e068160d8110382601401b001683301e068160d8110342601801b0015c5a01e068160d8110342601801b0015c078b0068160d8110342601801b000cc078c8068160d8110342601801b0015c0801e068160d8110342601801b000005701e068160d8110342601801a 0x15c0781a05836120120342601801b000005701e068160d8120342601801a0000053020068160d8480342601801a001b80781a058352f0120382601801b0001d3201a058362f0120382601801b0014c0781a058352f0480382601801b0006c5301e068160d4480382601801b0000008150068160d8120342601401a0000053150068160d8120342601401a0000000150068160d812034260140190006c53020068160d8120382601401b001b853020068160d8120342601801b0001d06a340588c0d8480480e09801b000cc4801e068160d8120382601401b000000781a0588c560110342601801a001b8078c8068160d8120342601801b0016853020068160d8120342601801b001684801e068160d8110382601801b0014c48020068160d8120382601401b000d40741a05836049400382601801b0001d06a34058362f0120382601801b001680781a0588c0d8115000e09801b000000801e06816230115000e09801a0014c0781a0588c0d8125000e09801b0001d3201a0588c0d8125000e09801b001480781a0588c0d8115000e09801b0001d06816230362f0480480e09801b000000741a05836045400382655001a000000741a0588c0d8110382655001a000000001d068160d811038265500190001d06816230362f0125000e09801b0006c531c0068160d4120382601402b) (bn (Nat.blt i 3) 0x741a0588c0d8a01200e09801a001200801e068161a0110382601402b001647001e068160d4120382601402b000d40741a05836280120382601801b001c0078b0068160d8a00382601402b001cc0781a05836045400382601802b000200781a05868045400382601802b0001d068160d8a00480e09805008dcb000000741a058360480e09805008dca001cc0781a05836280120382601402b000200781a05868280120382601402b0006c0781a058352f0120382601801b000c00741a058362f0120382601801b0001d2c01a058362f0a00382601801b0001d06816230362f0a00480e09801b000200781a058362f0120382601801b000000741a0588c0d8bc0480e09801a000000741a058351205c0382601801a000200781a05836280480382601801b0006c0781a05835280480382601801b000c00741a05836280480382601801b001b80781a05835280480382601801b0001d3201a05836280480382601801b00000074c8068160d8a00382601801a000000801e06816560110342601801a000000001e068165601103426018019000cc0801e06816230120342601801b000005302006816230120342601801a00020078c806816230120342601801b001200801e06816230110382601801b000200781a8d016230110382601801b0014c7001a05835049400382601802b (bn (Nat.blt i 4) 0x1147c01e068160d4110382601402b00000078b0068160d4114f02601801a000000001d068160d84c038260140190001d320b0068160d8a00382601801b000c0074b0068161a0120382601402b0019c3c01e068160d4120382601801b000cc53020068160d8120342601401b001680781a05836280120382601801b000200781a0588c280120382601801b000d40741a0588c0d8120382601801b0001d068160d8a00480e098062e001b0001d06816230360480e098062e001b000000741a058360480e098062e001a0001d3201a0588c0d8a00382601801b0019c0781a05835280120382601801b000f0078b0068160d8a00382601801b001cc7c01e068160d8110382601402b0014c7c1c0068160d4120382601402b001600781a05835045400382601802b001480781a058350457c0382601802b001140801e068160d8120382601401b00000074b0068160d84c0382601401a0006c0801a05836280120382601401b001140781a05836280120382601401b000cc078b0068160d8a00382601401b0006c078b0068160d8a00382601401b000c0074b0068160d8a00382601401b0001d2c01a058362804c0382601401b000000741a058362804c0382601401a000000781a058368e0120382601401a000000741a058352805c0382601801a000000001d068160d45c03826018019 0x120078b006816230110382601801b000201f0b006816230110382601801b001140781a05835120120382601801b000005b01e068160d4110382601801a001143c07c068160d4110382601801b000f01f240068160d4110382601801b0016c078b0068160d4110382601801b00114078c8068160d4110382601801b0016c078c8068160d4110382601801b0016c1f01e068160d4110382601801b0015c3c07c068160d4110382601801b00000079f4068160d4110382601402a000cc0781a058350457c0382601802b00138078b0068160d4110382601402b00114079bc068160d4110382601402b00138079bc068160d4110382601402b0019c078b0068160d4120382601801b000004e01e068160d4110382601402a0000007a44068160d4110382601402a00120079bc068160d8110382601402b000201f1bc068160d8110382601402b0006c079bc068160d4120382601402b00148079bc068160d4110382601802b001381f01e068160d4110382601402b0007c078c8068160d4120382601801b0006c078b0068160d4480382601801b001141f01e068160d4115002601801b0007c07a40068160d4115002601801b000201f0b0068160d8115002601801b000d41f01e068160d4115002601801b0007c0781a05835045408f02601801b0007c078b006816230360454009801b))) (bn (Nat.blt i 8) (bn (Nat.blt i 6) 0x1b81b01e068160d4120382601801b001981f01e068160d4110f02601402b0001e06816232540d8120342601801b000000781a05a540d8120342601801a001680781a8d0160d8110382601801b0001d3201a8d0160d8120382601801b0015c0781a0588c0d8120342601801b0007c0781a058350443c9402601402b000f01f0b0068160d4110f02601802b0007c078c8068160d4110f02601802b0007c078b0068161a0360443c09805b000001f01e2c01a058680443c09805a00160078b0068160d4110382601802b0001e2c01a058350440e0980600970b001140781a058350440e098fc01802b0015c078b0068160d8120342601801b0007c078b0068160d4115f02601802b000cc078c8068160d8120342601801b000c03301e068160d8120382601401b000c0074c8068160d8120382601801b000c0075bc068160d8120382601402b0007c0781a058350440e0980693002b0000007a48068160d4110382601801a00120078c8068160d8110382601801b000201f0c8068160d8110382601801b0006c078c8068160d4120382601801b001140781a0588c0d8110382601801b000f01f1bc068160d4110382601802b001a8078b0068160d8110382601801b0001e2c01a05836680110382601801b001681f0b0068160d8110382601801b0007c078c8068160d8110382601801b (bn (Nat.blt i 7) 0x7c078b0068161a0115002601802b001140781a058354c0120382601402b00164078b0068160d4120382601402b0007c079bc068160d4120382601402b001cc0781a390160d8110382601402b0001d2c01a290160d8a0098fc01802b001141f01e068160d4110f02601402b0007c07a40068160d4110f02601402b000201f0b0068160d8110f02601402b0006c078b0068160d4120f02601402b0001e2c01a058350443c6202601402b00000078b0068160d4116202601402a0006c078b0068160d5300382601402b0007c079bc068160d4115002601802b001140781a058680d8110382601402b0011c078b0068160d8110382601402b0001d2c01a058350480e0980646002b0007c079bc068160d8110382601402b0007c0781a058280d8110382601402b00120078b0068161a0110382601402b00148078b0068161a0110382601802b00114078b0068161a0110382601402b0001d2c01a058352800e0980693002b0011c078b0068161a0110382601402b0007c0781a058680a0110382601402b0007c078b0068160a0110382601402b000001f01e068160a0110382601402a0006c078b0068161a0120382601402b000201f0b0068161a0110382601402b001485a01e068160d8110382601801b000cc1b01e068160d8120382601401b00168078c8068160d8120342601801b 0x781a0583504a5c0382601801a0007c078c8068160d8120382601801b0006c1f01e068160d4480382601801b000001b01e068160d4480382601801a0007c0781a0588c0d8480480e09801b001201f01e068160d8115002601801b002583c07c068160d4110382601802b0006c1f01e068160d4125002601801b0007c078b0068160d8125002601801b000000781a05835045404f02601801a000001f01e068160d4114f02601801a000000001e068160d4114f0260180190007c0781a8d0160d8115002601801b000000807c068160d8115002601801a001a80781a0588c0d8110382601801b001a81f01e068160d8110382601801b000006a01e068160d8110382601801a0001e0681623036680110382601801b0007c0781a05836680110382601801b000000781a05836680110382601801a001681f01a0588c0d8110382601801b000005a07c068160d8110382601801a000004801e06816230110382601801a000000807c06816230110382601801a0006c0781a0588c0d8120382601801b001200781a05836120120382601801b000201f01a05836120120382601801b0019c0781a05835120120382601801b0019c1f01e068160d4120382601801b000006701e068160d4120382601801a001201f01e06816230110382601801b000f01f0b0068161a0110382601802b)) (bn (Nat.blt i 9) 0x6c1f01e068160d4120f02601402b001481f01e068160d4110f02601802b0007c078b0068160d8120f02601402b000000781a058350443c6202601402a000001f01e068160d4116202601402a000000001e068160d411620260140290007c0781a390160d8110f02601402b0007c0781a058357e0120f02601402b000001b01e068160d4120f02601402a001480807c068160d8110382601801b00148078b0068160d8120382601801b0007c0781a058352f0125002601801b000001f144068160d4110382601801a000003c144068160d4110382601801a0000000144068160d41103826018019001683c07c068160d8110382601801b000f04807c068160d8110382601801b001b83c07c068160d4120382601801b000f01b07c068160d4120382601801b000f01f0b0068160d8120382601801b0000008090068160d8110382601401a0000000090068160d81103826014019000cc0807c068160d8120382601401b001680807c068160d8110382601801b001cc0807c068160d8110382601402b0006c4801e068160d8120382601401b0006c0807c068160d8120382601401b001484801e068160d8110382601801b00114078b0068160d8120382601401b001141f01e068160d8120382601401b000004501e068160d8120382601401a000001b020068160d8120382601401a (bn (Nat.blt i 10) 0x207c07c068160d8110382601402b0006c7c01e068160d4120382601402b002580781a058350457c0382601802b000f07c07c068160d4110382601802b001f01f01e068160d4115002601802b001f0078b0068160d8120382601402b0014c0781a058350497c0382601802b000200781a058360457c0382601802b0011c0781a058680d8110382601402b0011c1f01e068160d8110382601402b000004701e068160d8110382601402a000003c07c068160d4110f02601802a0007c0781a0588c0d8110f02601802b0007c0781a05835120120f02601802b0007c0781a058350457c0f02601802b000001f01e068161a0360443c09805a001600781a058350440e098fc01802b000005801e068160d4110382601802a000000781a058350440e0980600970a0006c0781a058350480e098fc01802b001200781a058360440e098fc01802b000201f01a058360440e098fc01802b0007c0781a058350457c098fc01802b000001f01e068160d4115f02601802a0001e068160d411038263f00600970b0007c079bc068160d8120382601402b002580781a290160d8110382601802b000f01f01a058354c0120382601802b0007c0781a058354c0125002601802b0001d068a40583628012098fc01802b001201f01e068160d8110f02601402b000000807c068160d8110f02601402a 0x1200781a390160d8110382601402b000000741a29016230480480e09801a0014c0781a8d0160d8120382601801b001200781a29016230110382601801b001680781a29016230110382601801b000d40741a05836120120382601801b000000741a29016650110382601801a000000001d0681665011038260180190014c0781a29016230120382601801b000c00741a29016230120382601801b0001d3201a29016230120382601801b000000741a29016230a00482601801a0006c5301e068160d5300382601402b001b80781a290160d8120382601801b000000741a0588c650110382601801a000000741a058350480e0980646002a000000807c068161a0110382601402a0006c0781a058680d8120382601402b0007c078b0068161a0120382601402b001480781a058680d8110382601802b000f01f01a058680d8110382601802b000001f090068160d8110382601401a0007c0781a058680d8115002601802b001200781a058364c0120382601402b000201f01a058364c0120382601402b001640781a058354c0120382601402b001641f01e068160d4120382601402b000005901e068160d4120382601402a0801e068160d8a00480e098fc01802c000001f01e06816230360454009801a0007c0781a058350457c5002601802b001207c01e068160d8110382601402b)))) (bn (Nat.blt i 17) (bn (Nat.blt i 14) (bn (Nat.blt i 12) 0x1d068a4058362f0a00482601801b0001d068a4058367e0a00482601402b0001d6f01a058367e0120382601402b000c03c01e068160d8120382601801b000f00781a290160d8a00482601801b001a80781a290160d8110382601801b001200781a8d0160d8110382601801b000c00741a8d0160d8120382601801b001a83c01e068160d8110382601801b000200781a390161a0110382601402b001980741a05836280120382601402b000c00741a058367e0120382601402b0001d2c01a390161a0120382601402b0001d068e4058680d8a00482601402b001640781a05835280120382601402b0006c0781a058357e0120382601402b001145301e068160d8120382601401b0006c0781a290160d8a00482601401b001140781a290160d8120382601401b001200781a290160d8a00482601401b000d40741a290160d8120382601801b000003501d068160d8120382601801a0014c0781a290160d8480382601801b000000741a290160d8a01202601801a0001d06a34290160d8a00482601801b0011c7001e068160d8110382601402b0014c7001a290160d8120382601402b000c07001e068160d8120382601402b001c00781a290160d8a00482601402b002200781a05835049400382601802b0014c0781a058354c1400382601802b0011c0781a290160d8110382601402b (bn (Nat.blt i 13) 0x14c0781a058357e1300382601402b001980741a058364c0120382601402b002200781a290160d8120382601402b0014c0781a290160d9300382601402b000006601d068160d8120382601402a00198074b0068160d8120382601402b000000741a058350483c6402601402a000000741a05835280126402601402a000000001d068160d41264026014029000f00781a05835280120f02601802b0001d0681623036280120f02601802b000000741a05835280480f02601802a0001d068160d4a00497c0f02601802b0001d068160d4bc280120f02601802b000200781a058367e0120382601402b001680781a058360443c0382601802b000200781a0588c0443c0382601802b0011c0781a058360443c0382601402b001640781a058350483c0382601402b001f00781a390160d8110382601402b000000741a390160d8a00482601402a000200781a05836280120f02601402b0006c0781a05835280120f02601402b000c00741a05836280120f02601402b00000074b0068160d8a00f02601402a001f00781a05835280120f02601402b0001d068e405836280120f02601402b001f00781a058357e0120382601402b000c00741a290160d8a00482601401b000000741a05836280123602601401a000000741a290160d8123602601401a000000001d068160d81236026014019 0xc03c01e068160d4120382601801b000000741a058352820c0382601801a00000074b0068160d45c0382601801a000c07001e068160d4120382601402b001c00781a05835130120382601402b0014c700b0068160d4a00382601402b0001d2c01a0588c0d8a01200e09801b000cc0781a058352f0120382601801b000d40741a058352f0120382601801b000d4074b0068160d4120382601801b000003501d068160d4120382601801a000000741a058356b0120382601801a0014c078b0068160d4bc0382601801b00000074c8068160d4a00382601801a000cc0781a05835280480382601801b000c00741a05835280480382601801b0001d068160d4a01204c0382601801b000000741a058351204c0382601801a001b8078b0068160d4a00382601801b0001d3201a05835280480382601801b0001d320b0068160d4a00382601801b0001d2c01a0588c0d8bc0480e09801b000f00781a390160d8110382601802b001645301e068160d4120382601402b0014c080b006816230120342601801b000000741a058360440e0980600a60a0014c0781a390160d8120382601402b0006c5301e068160d4120f02601402b000cc0781a058360483c0382601402b0014c0801a058360483c0382601402b0011c0801e068160d8110382601402b0001d068e4290160d8a00482601402b)) (bn (Nat.blt i 15) 0x14c079bc068160d4a00382601402b0001d6f01a05836280120382601402b0001d068161a036130120382601402b0001d6f01a390160d8110382601402b00000078b0068160d4d00382601401a001980741a058680d8110382601402b0015c078b0068160d4a00382601801b000cc078c8068160d4a00382601801b00000074b0068160d4440382601801a0001d3201a058352804c0382601801b0015c078c8068160d4a00382601801b00020078c8068160d8a00382601801b0006c078c8068160d4a00382601801b000c0074c8068160d4a00382601801b000000741a058352809c0382601801a000f00781a058352804c0382601801b00114078b0068160d8a00382601401b000000801e068160d84c0382601401a000c0074c8068160d4120382601801b0015c0781a05835280120382601801b0014c078c8068160d4a00382601801b0001d3201a05836280120382601801b000c00741a0588c0d8120382601801b0001d0681623036130120382601801b0001d2c01a058360480e098062e001b000d40741a05835280120382601801b000c00741a058352f0120382601801b000000741a05835110120382601801a00000079e8068160d4a00382601401a0014c080b0068160d8a00382601401b00000078b0068160d5ec0382601401a000005301e068160d44c0382601401a (bn (Nat.blt i 16) 0xc03301e068160d4120382601401b000000781a05835340120382601401a000200781a058360440e8f02601801b000cc0781a05836120120342601801b0014c080b0068160d8480342601801b0001d3201a058352f0120382601801b0016c3301e068160d4110382601801b000000781a05835046640382601801a000cc0781a05836045400382601801b000cc0781a05835049400382601801b0016c0781a05835045400382601801b000d43301e068160d4110382601801b0001d068160d5ac049400382601801b00000074e8068160d4110382601801a000c05701e068160d4110382601801b000cc0781a0588c0d8115000e09801b0001d3201a0588c0d8115000e09801b00020078b006816230115000e09801b000d40741a0588c0d8115000e09801b0001d06816230360454003a3c09801b001c00781a058350440e8f02601802b00000074b0068160d8110382655001a0000007934068160d4a00382601401a0006c080b0068160d8a00382601401b00114078b0068160d4a00382601401b0001d2c01a058352809c0382601801b000200781a058362804c0382601401b00000074b0068160d8a00382601401a000000741a058c40d8110382601402a000c07301e068160d8110382601402b000c00801e068161a0110382601402b001d00781a05835280120382601402b 0xf00781a058350440e9402601802b001983301e068160d4110382601402b000cc0781a058350440e9402601402b001383301e068160d4110382601402b000000781a058350440e9d02601402a001983c01e068160d4110382601802b000000741a05a700d8110382601801a000c05a01e068160d8110382601801b000c00801e06816230110382601801b000d40741a05835120120382601801b000000741a058359b0120382601801a000c06e01e068160d4120382601801b000c05301e068160d4480382601801b000c00741a0588c0d8480480e09801b001387001e068160d4110382601402b001383001e068160d4110382601402b001d03001e068160d4110382601402b001140801e068160d8110382601401b001145301e068160d4120382601401b000c053020068160d8120382601401b000d40741a0588c0d8110382601801b000d40801e068160d8110382601801b000d45301e068160d4120382601801b0016c3c01e068160d4110382601801b0016c3001e068160d4110382601801b000009a01e068160d4110382601801a000200781a05836130120382601401b000006901e068160d4120382601401a000c0531c0068160d4120382601402b001d00781a05835045400382601802b000cc0781a05836280120382601401b001140781a05835280120382601401b))) (bn (Nat.blt i 20) (bn (Nat.blt i 18) 0x9e01e068160d4110382601402a0001d2c01a290160d8a04c02601402b0001d6f01a290160d8a00482601402b000c08801e068160d4120382601402b000c05301e068160d5300382601402b001980741a290160d8110382601402b000c00741a390160d8110382601402b000cc0781a290161a0110382601402b000000741a05a181a0110382601402a000000741a290160a0110382601402a000cc0781a058357e0120382601402b0015c0781a058350443c0382601802b000cc0781a058350483c0382601402b0001d2c01a058360440e0980600a60b001985301e068160d4120382601402b0014c0781a058350480e9402601402b0014c078b0068160d5f80382601402b0001d068168a0360443c0382601402b001980801e068160d8110382601402b000200781a058360440e9402601402b001380781a058350443c0382601402b001987c01e068160d4110382601402b001f00781a058350440e9402601402b000cc0781a05835280120f02601402b000cc0781a058360443c0382601402b0001d068e4058360440e9402601402b001980741a390160d8110382601402b00198074b0068160d8110382601402b000006601d068160d8110382601402a0001d2c01a05a280d8110382601402b000000741a05a280d8110382601402a000cc0781a390160d8110382601402b (bn (Nat.blt i 19) 0x1d2c01a05835280480f02601802b000cc078b0068160d4a00f02601402b00020078b0068160d8a00f02601402b0006c078b0068160d4a00f02601402b000c0074b0068160d4a00f02601402b0001d2c01a058352804c0f02601402b000000741a058352804c0f02601402a0001d3201a05835280120f02601802b00000240b0068160d8110382601401a000cc0807c068160d8110382601401b001140807c068160d8110382601401b000201f240068160d8110382601401b0007c07934068160d4120382601401b001141b01e068160d4120382601401b000004501e068160d4120382601401a0000007934068160d4120382601401a0006c080b0068160d8120382601401b001484501e068160d4110382601801b000000741a05835280440382601801a00114078b0068160d4120382601401b00114078b0068160d8110382601401b001144801e068160d8110382601401b000004501e068160d8110382601401a00000074b006816870110382601402a0001d2c01a290161a0a00482601402b00000074b0068a4058682802601402a000cc0781a05835281300382601402b00220078b0068160d4a00382601402b000c00741a058364c0120382601402b000c00741a05835280120f02601402b002780781a058350443c0382601402b00278078b0068160d4110382601402b 0x741a05828280120382601402a0001d2c01a05868130120382601402b0001d2c01a058680480e09805008dcb0014c078b0068161a0a00382601402b000cc078b0068161a0a00382601402b00020078b0068161a0a00382601402b0001d6f0b0068161a0a00382601402b0001d2c01a058682804c0382601402b00000074b0068161a04c0382601402a0001d2c01a058682800e09805008dcb001cc078b0068160d8a00382601402b00198074b0068160d4a00f02601402b0001d2c01a058352803c9402601402b00000074b0068e4058362802601402a0001d2c01a058357e0a00f02601402b00000074c8068160d4440382601801a000f0078b0068160d4a00f02601802b0001d320b0068160d4a00f02601802b00000074c8068160d4a00f02601802a0001d2c01a0588c0d8a00f02601802b0001d2c01a058352f0a00f02601802b00000074b0068161a0a00483c09805a000000001d2c01a058682803c09805900000074b0068160d4a06402601402a0001d068160d4a0130120f02601402b0014c078b0068160d4a00f02601402b001980741a05835280120f02601402b0001d068160d4a00483c9402601402b0001d2c01a390160d8a00482601402b0001d2c01a058350483c6402601402b00000074b0068160d4126402601402a000c0074b0068160d8a00f02601402b)) (bn (Nat.blt i 21) 0xcc0781a05868045400382601802b000c03301e068161a0110382601402b00000074b006816310110382601402a000007001e068160d44c0382601402a000000001d068160d44403826018019000c0074c8068160d8a00382601801b001143301e068161a0110382601402b00168078b0068160d8a00382601801b00020078b006816230a00382601801b0001d06816230362804c0382601801b0001d2c01a058362800e098062e001b0019c078b0068160d4a00382601801b000d4074b0068160d4a00382601801b000000741a05835281ac0382601801a000d4074b0068160d8a00382601801b0006c078b0068160d4bc0382601801b000000741a0588c0d84c0382601801a0006c078b0068161a0a00382601402b001cc078b0068161a0a00382601402b000cc0781a390161a0110382601402b00198074b0068161a0110382601402b000000741a05a281a0110382601402a001d0078b0068160d4a00382601402b00198074b0068161a0120382601402b0001d2c01a390161a0a00482601402b00000074b0068e4058682802601402a00164078b0068160d4a00382601402b0006c078b0068160d5f80382601402b000cc079bc068160d4a00382601402b000cc0781a05868280120382601402b0001d068161a028280120382601402b0001d2c01a05828280120382601402b (bn (Nat.blt i 22) 0x6c078b0068a4058362802601401b000cc0781a290160d8a00482601401b00000074b006816650110382601801a0001d2c01a29016230a00482601801b00000074b0068a40588c2802601801a000c00741a05836120120382601801b0001d3201a290160d8120382601801b0001d2c01a290160d8a01202601801b0001d2c01a29016230480480e09801b000c07001e068160d8110382601402b001c0078b0068a4058362802601402b000c0075bc068160d8110382601402b0001d6f0b0068a4058362802601402b001140781a290160d8110382601401b0001d3201a290160d8a00482601801b00000074c8068a4058362802601801a000d40741a290160d8110382601801b000c00741a8d0160d8110382601801b000cc0781a8d0160d8110382601801b000d40741a8d0160d8110382601801b000d4074b0068160d8110382601801b000000741a29016770110382601801a000cc0781a29016230110382601801b000c00741a29016230110382601801b000000741a05a18230110382601801a0001d3201a29016230110382601801b000003501d068160d8110382601801a0001d2c01a0588c0d8bc2800e09801b0001e2c27c068160d4a00382601402b001c00781a058352804c0382601402b001c0078b0068160d44c0382601402b001d00781a290160d8110382601402b 0xc0074b0068a4058362802601401b00000074b0068160d8a03602601401a0001d2c01a290160d8bc2802601801b0001d2c01a290160d9f82802601402b000c03c01e068160d8110382601801b000f0078b0068a4058362802601801b000c0074c8068160d8110382601801b0001d320b0068a4058362802601801b0015c0781a290160d8110382601801b0001d2c01a290160d8a01302601401b000000741a290160d8a01302601401a000000741a05a800d8110382601801a000c03301e068160d8110382601401b0001d068a4058362804c0482601401b00000074b0068160d8123602601401a0014c078b0068a4058362802601401b000cc078b0068a4058362802601401b)))))
def htd_S0_11 (i : Nat) : Nat := (bn (Nat.blt i 3) (bn (Nat.blt i 1) 0x4000000000000000002001001000000003001000000000000000002000000000002000001002000000000000000000000000000000000000001000000000001000005000000000000002004000000000000000000005000000001001001000000000000000000000001002000000000002000000003000000001000004000001000000003000000000000000000000000000003000000000001000000001000000000000003000000000000000001001000000000000000002000006 (bn (Nat.blt i 2) 0x1001002000000000000000000000000000000000001000001000000000001001000000000001000001000000000001000000000001001000001000002000000000000000005000000004002000002001001000000003000000000000002000000000001000000000002000000002006000002000000000000000002001000000000002000000001002000000001001000001001000000001000000000000000000000002000000000000000001000000000001000000000001000000 0x2001000006000000000000000004000000002001002000000000000000000000000000000000001000001001000001000000000000008000003000000000000000000001001001000000000000000001000000001002003000000000001000000000000001000000003000000000000000001000000000000000001000001000000000000007000000001000000000000000000001000000000003003000000001000000000006000000006001000000000000001002000000001000000)) (bn (Nat.blt i 4) 0x2000000000000006000002000001000000000000000000000000001003001000000001001000000000000000000005000001002000000001000000000000000000000000000000000002000000000000000000000006000000000000000003000001000000002000000000000000001000000003000001000000000000001002000001000001000000000000000001000000000001000000000000000004000000001000000000000000000000000000001000000000000000 (bn (Nat.blt i 5) 0x3000002000001000000000000001000001000000000000002002001000001000000001001000000000009001000002000000000002000000000001002000000000000000000000000001004000000001000000001002000000000000000000000000001000000000000001000000000000001000000000000000000000000000000000004000001002001000001000002000003004000000000000005001000000000000001000000002000000000000001004000000000002000000000 0x1000000000000000000000002000000001000000003000000000000003000003000001000000000000000002000000001000001000000000000001000000000001000000000004000001000000000000000000002000000005000000)))
def hta_S0_11 (i : Nat) : Nat := (bn (Nat.blt i 10) (bn (Nat.blt i 5) (bn (Nat.blt i 2) (bn (Nat.blt i 1) 0x23f4a2000c5c540009f0410000000000000000000210800562000000000000010a98700000000581000000005010000000050f74b33d69b5096eedc001af0000014e33c000000004f085e0000000044a00259842000bcccda5b006001a28971574ed9a8c043a000000003180000038f10114400000000db535c26000df58a8000000000054000000283ac13bab09550007b0000000001660000000097ebfe375498c610c0058b000000002ee 0x2bc0000022582f6c600000000a100000007b136a68db02041202c00000000000000000000000000069e0023ec1d1d418aa2cb217ecc4b1b4e378000000000000000002b6c94bc761cc1ae81400000000000004ec0000000000054a0000014f000000002a9490c5c000003bed32ac8000007acce449000d04002a65ea86c00000000000000008c86f54994e000000000f530563c4400053b0fd328000000000000000000229800) (bn (Nat.blt i 3) 0x110d5d8be10f4a61b8001fa0026e0370db5a4000000013e000007000e368d8000000000001d00055c0000000000096161000000000008d80000000000000000000000000004a9000000000000007ed70800001658000000000000028900000000000000000003be41e000000000000000000000000000000000974000000000000017c6be00000000000000000006dc00000000000002118000000000000000105000000068000001b500000000000 (bn (Nat.blt i 4) 0x43c89c0000024ca647800000052c0000040e0007c000000c3c0023d00000000000000000000000002e22e000000710003fb5d60000053d08e00000155000000000001d600000000000e44000000420027380077e35487000000000002980000000000000119e8f8000002d4a6bc27ce000d68000000000000051e000bd8000000000005300000000000000000000000000000038198a000001030000000000003706000000000000004a100000000000 0x174000008364349180000000276800658334001db000a060780072a000000003a4d6a6fa62ada000000001e4002409719eecae3491b0282444a2c97752b40000000000000387000000000004ab54d09c41050f90003a30000000028d140be856800000000889d00d673a3d0007c0c74000008320000019d000000001c100079000000000000000000000000024d000000000006ab53a0880000018ec18000000000000092f30000000))) (bn (Nat.blt i 7) (bn (Nat.blt i 6) 0x92000003217d6c4c00000000000000000000014329400000279000000000000003aa2dc00000000f94000000000020b800000000004d7000000000007de000000006e4758768004decbc000000000028c39b06a00000000126e1484b0b5fa0000000000000000057acece8e3800000000e9800268000000002fc4a6ba800572afe558000000012a0000000000501f000000000006f7438000002d73c54280000000131c2a 0x1671d0c79000002cf8003240028880000043c82800000af40000000000000000000000928009c14d00000000000000000000000001240000004ac0300000172800046d5e41237000148003ff000000ee259000000588000003d8a28d1000ddc00000000614003df00123c0047c000001580000015fcb48000013a29c800ac613cc7c3358d1be468cb0000000000000091c000006ba000004440015840000018e0000000000000000000) (bn (Nat.blt i 8) 0x1a447bfd0000024729f000000000bd000d60004ff0000000000033c5b845117000905cc57100001521800000918002af69647e23800000000001962baf44005a159c0023a800000cdcca000000580000000000000058d1cf2419f36b1320000000082a002ae80077828c000000000000050c00000000000000000002f1546c6c9d80078842c00000652000000000015ac0000094a0013c800000001e380083e000b8059000001fc5231f499a8bc5d (bn (Nat.blt i 9) 0xed177800000000000003520000024c9df0f0448ef0000000000000000000000812001454f9000b65fb000000001aa0000000000028ea2ac24000000001e264000000d440057386a000000000000002f8003c7154003e30000000000075e0022b0000000028158700000000000186000ea0004595080012d001384378006cf138003e985a0000000079e000000000000000000015c000000000000000000000144c0057d9125900000043f21400000 0x7aa00099800000000000000011643e800000210000000013f4005250004bc8aab70010c40000000000000000000000000000015d27d8a4000000000009e67bcdc0000000000036139f4199e80000000225000766000000000000000000077200000000922000000000009140036c000eac00000b32000001280000000000027a000d02d60015c0000005f2000004e4000000002cd9cc2d0000008f00000000000000000000000e4062800)))) (bn (Nat.blt i 15) (bn (Nat.blt i 12) (bn (Nat.blt i 11) 0x589c562118a82000000003b05440000000117888393000000000000000000033b000b280000002e7fa9883100000000000876000001ca1f67e800000000000bc1a50000000000000000000000000000df2a80008bc8b521000000000000000000000000000000000000000002830000640000000000000333138384cc80000038c00000a3a000133d7038000002970000000019539600000000000000001e90000000000014e82c0000093a00000a1a 0x2abb27a16b981f8dc4b400000295ad51fc00000067358044dd0000000046da340000049b9ed65e9f8dba096140000000068800000000000000419928a4000000000000025080e00000000000a200018a0000000000082600050b24aa21fc000004791cd53a6d6860000012b0011dc004e3000bf04faad8c05d8000000000000000077a00249b2a000296ac0003b44790bd0a0002bc005651ca000002030013a534127000b6c3b519) (bn (Nat.blt i 13) 0x16d000c96650000008b400000000000000000007c400420724c7148800000ed80000000000282800000000003c300000000000000dd56a0008f71f80000000088400000000000000000000000000000041c000110000000000000127cb793a07a784001f445600000591000000000004620ee7a4d300000000000000dc400000182000002612fb4d5eccc13ae00000232000000000000000005db2d3f262000000000000000002a600186800 (bn (Nat.blt i 14) 0x25a8000000024a96523b184000000000000037400000000000000001b780013a000000009d4000099a16cb200d5b799ea001cb3b5000001d8ba997b5eaa42dd8be76400000976bb1900a200000000223000000000000000000000000000000000000dd889b2e000da130000b3a00000328000000000000000012b8000006e4000009aa1c400015000000000000000006c800764001a4000a0600045a56000000000002403fc0040d00000000499 0x910d1cd22c55a2c1e68800000000000000000000000038a78a464c7af2a400000028e000000000000000004c000000001ff4a5396030e9a9e9d6bb800000000000ee8e46393b0006d2000003ed0000008d359000002a3ac726000000000174000000002be000c6935000000002c80002e400000000c8a3157b516d980000000000257b054e69a800000000000000007382483e0000006c65380d22800000000000000000002b50ac00000000eb612865))) (bn (Nat.blt i 18) (bn (Nat.blt i 16) 0xf161ca580000013f9bb000fea41b49000000000000a000000509000000000006311080014a00059de58007760000000000000000000000e68cd1c987cab00053700000000000001400003100000020080000000000000000000000000000013a000596000fb800000000000000000000000000000000000000fdc00000000000000000ac00000000000ce4002cc0000000045880a924cc1bf6e6f840046600113c0000000113226989000ae1380d3 (bn (Nat.blt i 17) 0x2b294e75ccd12c000000000014ac00000000000fc287000001e3000000001cc800350000000003840000000000c5e4d9800000000000008e3121ed800000000000000000007000000000000000000001c4800000fe40000009a93c000835bf11645c289bca88079d100070ea688557c3dc000b200000000000000000003f100000155b5300000000000000000000006323a0003c15d200293b0a0000000023534755508800000000000002e800000000 0x147a6cc57000000990000009f400197000001ab0002781d0000000002a40000000000000484000000003970000007980000000000000000000002920000022d0000011ac00000000000000000000019180011a000000000001cc0043d7ba0005e00000109e2d800000001ca0000d000000029232c7c00000a38fa8000003bcba0b50000000000000000009c000000000016780008b655e019027200000000000000b9800000000000000007ce89137)) (bn (Nat.blt i 19) 0xa6d80000000000589000000e6a4a000b5c003d3602001c1a6c000a780015b0000013bb030003889f80000000000000b362da453cd000488000000000000000043200000000000000000000000000000000050480a9b000000000000000000000000000056000000000fea672e40011d800680146a60000000000037f000000000002fe00000000000001d6429000000b60000000027d1a63063e4000091e345000000000000002720000000024b (bn (Nat.blt i 20) 0x19e001f98000012c40000000000000000000000002f700102c002b584800261b9f3cf50c00000811330001e585c558000003ea525ce8000009a500d931028366d44656c000001211927b532311000000f01a70000006f0000000000000000000299800000b0c0035c000000004126b6000000007920000000074ea817180000050e5c8000000000038b262508e04cb46752c000000000000025f00000000000abf21d6ad3e 0x2b3b240000000000000000000000000000000000000000000000000000000000000000000000055b0ab434000000000001700000000073000adf5a03d0000000001c8000006e8c880038c000004a30014b4000000008e4000000b693800000000000000000000000000000000000000)))))
def st_S0_12 (i : Nat) : Nat := (bn (Nat.blt i 3) (bn (Nat.blt i 1) 0x74b0068a405836120120382601801c7001e2c01a290160d8110382601402c0001d6f01a290160d8110382601402b0001d2c01a290161a0110382601402b000006601d068160d4110382601402a074b0068e4290160d8110382601402c0007c079bc068160d4110382601402b1f01e2c01a058680d8110382601402c0007c078b0068161a0110382601402b1f01e2c01a058354c0120382601402c0007c078b0068160d4110f02601402b000cc078b0068160d8120342601401b1f01e6f0b0068160d4110382601402c001683c01e068160d8110342601801b000f0078b0068160d8120342601801b001483c01e068160d4110382601801b000c0074b0068160d8120382601401b0007c07a40068160d4110382601401b0000007a40068160d4110382601401a00120078b0068160d8110382601401b000201f0b0068160d8110382601401b0006c078b0068160d4120382601401b5207c078b0068160d4110382601801c00148078b0068160d4110382601801b000f01f0b0068160d4110382601801b1f01e320b0068160d4110382601801c0007c078c8068160d4110382601801b1f01e2c01a0588c0d8110382601801c1f01e2c01a05835120120382601801c0007c078b0068160d4115002601801b7c07c078b0068160d4110382601402c001f0078b0068160d4110382601402b (bn (Nat.blt i 2) 0x1f01e068160d4110f02601402a000000741a8d0160d8110382601801a000000741a29016230110382601801a0001d068a405836120120382601801b0001d068a4058364c0120382601402b0001d2c01a058360483c0382601402b000000807c068160d8110382601401a000000741a390160d8110382601402a000f00781a058350443c0382601802b0014c0781a058350483c0382601402b000200781a058360443c0382601402b001f00781a058350443c0382601402b000000741a05835280120f02601402a000004801e068160d8110382601401a0001d068e4058360443c0382601402b000000741a058350440e9402601402a074b0068e4058360443c0382601402c0001d2c01a390160d8110382601402b3c01e2c01a058350443c0382601802c3301e2c01a058350443c0382601402c000cc0781a058350443c0382601402b5301e2c01a058350483c0382601402c0001e2c240068160d4110382601401b7c01e2c01a058350443c0382601402c0001d2c01a05835280120f02601402b00000074b0068160d4a00f02601402a00114078b0068160d4110382601401b000004501e068160d4110382601401a0801e2c01a058360443c0382601402c0001d3201a290160d8110382601801b0001d2c01a8d0160d8110382601801b0001d2c01a29016230110382601801b 0x1d2c01a058350440e8f02601801b000000741a058350440e8f02601801a5201e2c01a05835045400382601801c00000074b0068160d8a00382601401a000f00781a05835280120382601801b000000741a058352f0120382601801a001c00781a05835280120382601402b0014c0781a290160d8120382601401b000003001d068160d8120382601401a000000741a290160d8a00482601401a000000741a05835280480382601801a000003301e068160d8120342601401a0000053020068160d8120342601401a000005a01e068160d8110342601801a000000801e06816230110342601801a000200781a05836120120342601801b000200781a05836280120382601401b0014c0781a05835049400382601801b0001d2c01a05836049400382601801b000000741a0588c0d8115000e09801a001c00781a05835045400382601802b000200781a05836045400382601801b000001b01e068160d4120382601401a0007c078b0068160d8120382601401b000005201e068160d4110382601801a000003c07c068160d4110382601801a000f00781a290160d8110382601801b0007c0781a05835120120382601801b000001f01e068160d4115002601801a000007c01e068160d4110382601402a0007c0781a058680d8110382601402b0007c0781a058354c0120382601402b)) (bn (Nat.blt i 4) 0x1d2c01a058352f0a00382601801b000000741a058352804c0382601401a3301e2c01a0588c0d8110342601801c000cc0781a0588c0d8110342601801b3c01e2c01a290160d8110382601801c000003301e068160d8110342601401a0014c080b0068160d8120342601401b00168078b0068160d8110342601801b5a0f0078b0068160d8110342601801c520f0078b0068160d4110382601801c000003301e068160d4120342601401a000cc078c8068160d4110342601801b000005701e068160d4110342601801a7c1c0078b0068160d4110382601402c300cc078b0068160d4110382601401c000c03301e068160d4110382601401b0801e320b0068160d8110342601801c000d4074b0068160d4110382601801b300f0078b0068160d4110382601801c3001d320b0068160d4110382601801c000c0074c8068160d4110382601801b3001d2c01a0588c0d8110382601801c3001d2c01a05835120120382601801c301c0078b0068160d4110382601402c00020078c8068160d8110342601801b00020078b006816230110342601801b3301e2c01a05835045400382601801c000cc0781a05835045400382601801b0801e2c01a05836045400382601801c5301e2c01a05835049400382601801c0001d2c01a0588c0d8115000e09801b0001d068160d4115000e8f02601801b (bn (Nat.blt i 5) 0xc07001e068160d4110382601402b3301e2c01a05835280120382601401c000cc0781a05835280120382601401b0801e2c01a05836280120382601401c1b01e2c01a05835280120382601401c000c00741a0588c0d8110382601801b000c0074b0068161a0110382601402b0001d2c01a05868280120382601402b0001d2c01a390161a0110382601402b000cc0781a290160d8110382601401b000c0075bc068160d4110382601402b000003001d068160d8110382601401a5301e2c01a290160d8120382601401c0001d2c01a290160d8a00482601401b00000074b0068a4058362802601401a074c82c01a290160d8110382601801c000c00741a058680d8110382601402b074b0068161a036280120382601402c074b0068e4058680d8110382601402c000cc078b0068160d4a00382601401b00020078b0068160d8a00382601401b0006c078b0068160d4a00382601401b000c0074b0068160d4a00382601401b0001d2c01a058352804c0382601401b001c0078b0068160d4a00382601402b00000074b0068160d44c0382601401a000000001d068160d44c03826014019000c0074b0068160d8a00382601401b000f0078b0068160d4a00382601801b0001d320b0068160d4a00382601801b00000074c8068160d4a00382601801a0001d2c01a0588c0d8a00382601801b 0x3c01e2c01a05835280120382601801c000003001d068160d4120382601401a0001d068160d4a0130120382601401b0001d2c01a05835130120382601401b000000741a05835130120382601401a0014c078b0068160d4a00382601401b074c82c01a05835280120382601801c0001d3201a05835280120382601801b074b0068160d4bc280120382601801c0001d2c01a058352f0120382601801b0001d2c01a05835280480382601801b3001d2c01a058680d8110382601402c000c00801e068160d8110382601401b000c05301e068160d4120382601401b000003501d068160d4110382601801a000c03c01e068160d4110382601801b7001e2c01a05835280120382601402c000c00741a05835120120382601801b)))
def htd_S0_12 (_ : Nat) : Nat := 0x40000c010000002000101800000000800010000002050000400020580000000180002000000800020180000010000808000080004020100408000080000010000406020000014000180c00000000006010600800000000408000000408000080000010000000000000004030000000030000000000000c0000010000000000000002040000800008100001
def hta_S0_12 (i : Nat) : Nat := (bn (Nat.blt i 2) (bn (Nat.blt i 1) 0x2dd7e00000018e0000496ba000002524ac9845c000000000006943800000000000007f0000089480000000b4a90a400000042000003e8002e0029a0800f21800800f10397854421ca5400617c4b63356000009e00001ac0020a98004c3a3bb12b20045115b8b182800016300001394f5dd7c22008fad8003b9a540012300000005100000000000001927a529c99ede 0x682e001430000000000024c000016a9dba0d00000ac0040000000073002c336003b6a2000009c0141002f4000000000a0000007c00fb56802b6526da8c006f30174000000000000000000fc0059801ea190000000a90000174d5000005600398010c050db9d4c0000225c0aa3e5900000460002a00004a5e667003e55e2c09ac00000990026e37275140146000020600) (bn (Nat.blt i 3) 0x1e800000000001821295800003e6283a40ce6a47001062d4e44a55690027f15008006200080889000618280079a3800010289a0644283702c010d2f8000000998c800f75ab8e620046885b4330000222fc9e80000000028400413400000006c800c84b6b1aaae7142800008e69800006c0ea6c0000000000000329d69c00003bd9a2f9a801d65b0000000d1770011709 0xae0087d10000348a40014b00000000c4e90e84a48227c5c58001b400004d0000000a000000234c801560041a3eb0002691c8cff74ae5e03431c2e429700001080893800000070c1c00001fb6000007ebea760000534011d1a9ec7910aad2596d78092400402c801be0f))
def st_S0_13 (_ : Nat) : Nat := 0xf0078b0068160d4110342601801b3301e2c01a058350440d09805006d4c078b0068160d4120342601401b0801e2c01a058360440d09805006c1d2c01a05835045400382601801b3001d2c01a058350440e09805006c003001d068160d4110382601401a074b0068160d4a00480e09805006c00074b0068160d4a00382601401a074b0068a4058360440e09805006c001f01e068160d4110382601401a0001d068a4058360440e098050068003301e068160d4110342601401a0001d068160d4a00480e098050068000741a05835045400382601801a000200781a058360440d098050068005301e068160d4120342601401a1f01e2c01a058350440e09805006c1d2c01a058350443c0382601402b
def htd_S0_13 (_ : Nat) : Nat := 0x102184001001180044
def hta_S0_13 (_ : Nat) : Nat := 0x95e55634068c04f6647dd1a000a5c000e8490004c021c5181430040070008d18806d240b
def st_S0_14 (_ : Nat) : Nat := 0x1d068160d41103426014019
def htd_S0_14 (_ : Nat) : Nat := 0
def hta_S0_14 (_ : Nat) : Nat := 0x10
def decW_S0 (e : Nat) : W :=
  let s := Nat.shiftRight e 2; let c := Nat.shiftRight s 4; let off := Nat.mul (Nat.land s 15) 144
  let p := Nat.land (Nat.shiftRight (wp_S0 c) off) top_S0; let n := Nat.land (Nat.shiftRight (wn_S0 c) off) top_S0
  ⟨p, n, Nat.land e 3, Nat.land p (Nat.xor n top_S0)⟩
def decWList_S0 : Nat → Nat → List W
  | 0, _ => []
  | n + 1, raw => decW_S0 (Nat.land raw 1023) :: decWList_S0 n (Nat.shiftRight raw 10)
lemma decWList_S0_ok : ∀ n raw, WOk top_S0 (decWList_S0 n raw)
  | 0, _ => wOk_nil
  | n + 1, raw => wOk_cons rfl (decWList_S0_ok n _)
def cnt_S0 (k : Nat) : Nat := (bn (Nat.blt k 12) (bn (Nat.blt k 10) (bn (Nat.beq k 9) (54) 0) (bn (Nat.blt k 11) (bn (Nat.beq k 10) (281) 0) (bn (Nat.beq k 11) (721) 0))) (bn (Nat.blt k 13) (bn (Nat.beq k 12) (178) 0) (bn (Nat.blt k 14) (bn (Nat.beq k 13) (19) 0) (bn (Nat.beq k 14) (1) 0))))
def decSt_S0 (k idx : Nat) : List W := (match Nat.blt k 12 with | true => (match Nat.blt k 10 with | true => (match Nat.beq k 9 with | true => (stProbe 94 st_S0_9 decWList_S0 idx) | false => []) | false => (match Nat.blt k 11 with | true => (match Nat.beq k 10 with | true => (stProbe 104 st_S0_10 decWList_S0 idx) | false => []) | false => (match Nat.beq k 11 with | true => (stProbe 124 st_S0_11 decWList_S0 idx) | false => []))) | false => (match Nat.blt k 13 with | true => (match Nat.beq k 12 with | true => (stProbe 124 st_S0_12 decWList_S0 idx) | false => []) | false => (match Nat.blt k 14 with | true => (match Nat.beq k 13 with | true => (stProbe 114 st_S0_13 decWList_S0 idx) | false => []) | false => (match Nat.beq k 14 with | true => (stProbe 94 st_S0_14 decWList_S0 idx) | false => []))))
lemma decSt_S0_ok (s idx : Nat) : WOk (2 ^ (12 * 12) - 1) (decSt_S0 s idx) := by
  have htop : (2 ^ (12 * 12) - 1) = top_S0 := by decide +kernel
  rw [htop]; unfold decSt_S0; repeat (first | apply wOk_match | exact wOk_nil | exact decWList_S0_ok _ _)
def lookup_S0 (k : Nat) (zs : List W) : Nat := (match Nat.blt k 12 with | true => (match Nat.blt k 10 with | true => (match Nat.beq k 9 with | true => (htProbe 1 103 1 391 9 511 7 127 htd_S0_9 hta_S0_9 zs) | false => 0) | false => (match Nat.blt k 11 with | true => (match Nat.beq k 10 with | true => (htProbe 1 380 31 1430 11 2047 10 1023 htd_S0_10 hta_S0_10 zs) | false => 0) | false => (match Nat.beq k 11 with | true => (htProbe 4 703 3 2641 12 4095 11 2047 htd_S0_11 hta_S0_11 zs) | false => 0))) | false => (match Nat.blt k 13 with | true => (match Nat.beq k 12 with | true => (htProbe 1 126 3 478 9 511 9 511 htd_S0_12 hta_S0_12 zs) | false => 0) | false => (match Nat.blt k 14 with | true => (match Nat.beq k 13 with | true => (htProbe 1 12 13 48 6 63 6 63 htd_S0_13 hta_S0_13 zs) | false => 0) | false => (match Nat.beq k 14 with | true => (htProbe 1 1 1 5 3 7 1 1 htd_S0_14 hta_S0_14 zs) | false => 0))))
def applyG_S0 (g : Nat) (zs : List W) : List W := match g with
  | 1 => mapInv fixP_S0_1 swP_S0_1 fixN_S0_1 swN_S0_1 zs
  | _ => zs
lemma applyG_S0_sound (g s : Nat) (zs : List W)
    (hrc : ∀ w ∈ zs.map W.toPNT, RowColConst 12 12 w.1 w.2.1)
    (hnat : NatTRestricted (2 ^ (12 * 12) - 1) s (zs.map W.toPNT)) :
    (∀ w ∈ (applyG_S0 g zs).map W.toPNT, RowColConst 12 12 w.1 w.2.1) ∧ NatTRestricted (2 ^ (12 * 12) - 1) s ((applyG_S0 g zs).map W.toPNT) := by
  rcases g with _ | _ | g
  · exact ⟨hrc, hnat⟩
  · exact inv_list_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) hrc hnat
  · exact ⟨hrc, hnat⟩
def certHit_S0 (k : Nat) (zs : List W) : Bool :=
  let code := lookup_S0 k zs
  match Nat.beq code 0 with | true => false | false => let c := Nat.sub code 1; let q := Nat.shiftRight c 1; match Nat.blt q (cnt_S0 k) with | false => false | true => isPermW (applyG_S0 (Nat.land c 1) zs) (decSt_S0 k q)
lemma certHit_S0_sound (s : Nat) (zs : List W)
    (hrc : ∀ w ∈ zs.map W.toPNT, RowColConst 12 12 w.1 w.2.1)
    (hnat : NatTRestricted (2 ^ (12 * 12) - 1) s (zs.map W.toPNT)) (hhit : certHit_S0 s zs = true) :
    ∃ idx < cnt_S0 s, (∀ w ∈ (decSt_S0 s idx).map W.toPNT, RowColConst 12 12 w.1 w.2.1) ∧ NatTRestricted (2 ^ (12 * 12) - 1) s ((decSt_S0 s idx).map W.toPNT) := by
  unfold certHit_S0 at hhit; dsimp only at hhit
  cases h0 : Nat.beq (lookup_S0 s zs) 0 <;> simp only [h0] at hhit
  · cases h1 : Nat.blt (Nat.shiftRight (Nat.sub (lookup_S0 s zs) 1) 1) (cnt_S0 s) <;> simp only [h1] at hhit
    · contradiction
    · have hp := isPermW_sound hhit
      have ⟨h1a, h2a⟩ := applyG_S0_sound (Nat.land (Nat.sub (lookup_S0 s zs) 1) 1) s zs hrc hnat
      exact ⟨_, by simpa [Nat.blt_eq] using h1, fun w hw => h1a w (hp.mem_iff.2 hw), natTRestricted_perm hp h2a⟩
  · contradiction
def chk_S0 (k idx : Nat) : Bool :=
  match stepExpand top_S0 12 m1_S0 m2_S0 m4_S0 m8_S0 rs_S0 rf_S0 certHit_S0 k (decSt_S0 k idx) with | true => false | false => true
lemma c_S0_9_0 : span (chk_S0 9) 24 0 = true := by decide +kernel
lemma c_S0_9_1 : span (chk_S0 9) 24 24 = true := by decide +kernel
lemma c_S0_9_2 : span (chk_S0 9) 6 48 = true := by decide +kernel
lemma all_S0_9 : ∀ i, 0 ≤ i → i < 54 → chk_S0 9 i = true := rj (rj (sr rfl c_S0_9_0) (sr rfl c_S0_9_1)) (sr rfl c_S0_9_2)
lemma c_S0_10_0 : span (chk_S0 10) 24 0 = true := by decide +kernel
lemma c_S0_10_1 : span (chk_S0 10) 24 24 = true := by decide +kernel
lemma c_S0_10_2 : span (chk_S0 10) 24 48 = true := by decide +kernel
lemma c_S0_10_3 : span (chk_S0 10) 24 72 = true := by decide +kernel
lemma c_S0_10_4 : span (chk_S0 10) 24 96 = true := by decide +kernel
lemma c_S0_10_5 : span (chk_S0 10) 24 120 = true := by decide +kernel
lemma c_S0_10_6 : span (chk_S0 10) 24 144 = true := by decide +kernel
lemma c_S0_10_7 : span (chk_S0 10) 24 168 = true := by decide +kernel
lemma c_S0_10_8 : span (chk_S0 10) 24 192 = true := by decide +kernel
lemma c_S0_10_9 : span (chk_S0 10) 24 216 = true := by decide +kernel
lemma c_S0_10_10 : span (chk_S0 10) 24 240 = true := by decide +kernel
lemma c_S0_10_11 : span (chk_S0 10) 17 264 = true := by decide +kernel
lemma all_S0_10 : ∀ i, 0 ≤ i → i < 281 → chk_S0 10 i = true := rj (rj (rj (rj (rj (rj (rj (rj (rj (rj (rj (sr rfl c_S0_10_0) (sr rfl c_S0_10_1)) (sr rfl c_S0_10_2)) (sr rfl c_S0_10_3)) (sr rfl c_S0_10_4)) (sr rfl c_S0_10_5)) (sr rfl c_S0_10_6)) (sr rfl c_S0_10_7)) (sr rfl c_S0_10_8)) (sr rfl c_S0_10_9)) (sr rfl c_S0_10_10)) (sr rfl c_S0_10_11)
lemma c_S0_11_0 : span (chk_S0 11) 16 0 = true := by decide +kernel
lemma c_S0_11_1 : span (chk_S0 11) 16 16 = true := by decide +kernel
lemma c_S0_11_2 : span (chk_S0 11) 16 32 = true := by decide +kernel
lemma c_S0_11_3 : span (chk_S0 11) 16 48 = true := by decide +kernel
lemma c_S0_11_4 : span (chk_S0 11) 16 64 = true := by decide +kernel
lemma c_S0_11_5 : span (chk_S0 11) 16 80 = true := by decide +kernel
lemma c_S0_11_6 : span (chk_S0 11) 16 96 = true := by decide +kernel
lemma c_S0_11_7 : span (chk_S0 11) 16 112 = true := by decide +kernel
lemma c_S0_11_8 : span (chk_S0 11) 16 128 = true := by decide +kernel
lemma c_S0_11_9 : span (chk_S0 11) 16 144 = true := by decide +kernel
lemma c_S0_11_10 : span (chk_S0 11) 16 160 = true := by decide +kernel
lemma c_S0_11_11 : span (chk_S0 11) 16 176 = true := by decide +kernel
lemma c_S0_11_12 : span (chk_S0 11) 16 192 = true := by decide +kernel
lemma c_S0_11_13 : span (chk_S0 11) 16 208 = true := by decide +kernel
lemma c_S0_11_14 : span (chk_S0 11) 16 224 = true := by decide +kernel
lemma c_S0_11_15 : span (chk_S0 11) 16 240 = true := by decide +kernel
lemma c_S0_11_16 : span (chk_S0 11) 16 256 = true := by decide +kernel
lemma c_S0_11_17 : span (chk_S0 11) 16 272 = true := by decide +kernel
lemma c_S0_11_18 : span (chk_S0 11) 16 288 = true := by decide +kernel
lemma c_S0_11_19 : span (chk_S0 11) 16 304 = true := by decide +kernel
lemma c_S0_11_20 : span (chk_S0 11) 16 320 = true := by decide +kernel
lemma c_S0_11_21 : span (chk_S0 11) 16 336 = true := by decide +kernel
lemma c_S0_11_22 : span (chk_S0 11) 16 352 = true := by decide +kernel
lemma c_S0_11_23 : span (chk_S0 11) 16 368 = true := by decide +kernel
lemma c_S0_11_24 : span (chk_S0 11) 16 384 = true := by decide +kernel
lemma c_S0_11_25 : span (chk_S0 11) 16 400 = true := by decide +kernel
lemma c_S0_11_26 : span (chk_S0 11) 16 416 = true := by decide +kernel
lemma c_S0_11_27 : span (chk_S0 11) 16 432 = true := by decide +kernel
lemma c_S0_11_28 : span (chk_S0 11) 16 448 = true := by decide +kernel
lemma c_S0_11_29 : span (chk_S0 11) 16 464 = true := by decide +kernel
lemma c_S0_11_30 : span (chk_S0 11) 16 480 = true := by decide +kernel
lemma c_S0_11_31 : span (chk_S0 11) 16 496 = true := by decide +kernel
lemma c_S0_11_32 : span (chk_S0 11) 16 512 = true := by decide +kernel
lemma c_S0_11_33 : span (chk_S0 11) 16 528 = true := by decide +kernel
lemma c_S0_11_34 : span (chk_S0 11) 16 544 = true := by decide +kernel
lemma c_S0_11_35 : span (chk_S0 11) 16 560 = true := by decide +kernel
lemma c_S0_11_36 : span (chk_S0 11) 16 576 = true := by decide +kernel
lemma c_S0_11_37 : span (chk_S0 11) 16 592 = true := by decide +kernel
lemma c_S0_11_38 : span (chk_S0 11) 16 608 = true := by decide +kernel
lemma c_S0_11_39 : span (chk_S0 11) 16 624 = true := by decide +kernel
lemma c_S0_11_40 : span (chk_S0 11) 16 640 = true := by decide +kernel
lemma c_S0_11_41 : span (chk_S0 11) 16 656 = true := by decide +kernel
lemma c_S0_11_42 : span (chk_S0 11) 16 672 = true := by decide +kernel
lemma c_S0_11_43 : span (chk_S0 11) 16 688 = true := by decide +kernel
lemma c_S0_11_44 : span (chk_S0 11) 16 704 = true := by decide +kernel
lemma c_S0_11_45 : span (chk_S0 11) 1 720 = true := by decide +kernel
lemma all_S0_11 : ∀ i, 0 ≤ i → i < 721 → chk_S0 11 i = true := rj (rj (rj (rj (rj (rj (rj (rj (rj (rj (rj (rj (rj (rj (rj (rj (rj (rj (rj (rj (rj (rj (rj (rj (rj (rj (rj (rj (rj (rj (rj (rj (rj (rj (rj (rj (rj (rj (rj (rj (rj (rj (rj (rj (rj (sr rfl c_S0_11_0) (sr rfl c_S0_11_1)) (sr rfl c_S0_11_2)) (sr rfl c_S0_11_3)) (sr rfl c_S0_11_4)) (sr rfl c_S0_11_5)) (sr rfl c_S0_11_6)) (sr rfl c_S0_11_7)) (sr rfl c_S0_11_8)) (sr rfl c_S0_11_9)) (sr rfl c_S0_11_10)) (sr rfl c_S0_11_11)) (sr rfl c_S0_11_12)) (sr rfl c_S0_11_13)) (sr rfl c_S0_11_14)) (sr rfl c_S0_11_15)) (sr rfl c_S0_11_16)) (sr rfl c_S0_11_17)) (sr rfl c_S0_11_18)) (sr rfl c_S0_11_19)) (sr rfl c_S0_11_20)) (sr rfl c_S0_11_21)) (sr rfl c_S0_11_22)) (sr rfl c_S0_11_23)) (sr rfl c_S0_11_24)) (sr rfl c_S0_11_25)) (sr rfl c_S0_11_26)) (sr rfl c_S0_11_27)) (sr rfl c_S0_11_28)) (sr rfl c_S0_11_29)) (sr rfl c_S0_11_30)) (sr rfl c_S0_11_31)) (sr rfl c_S0_11_32)) (sr rfl c_S0_11_33)) (sr rfl c_S0_11_34)) (sr rfl c_S0_11_35)) (sr rfl c_S0_11_36)) (sr rfl c_S0_11_37)) (sr rfl c_S0_11_38)) (sr rfl c_S0_11_39)) (sr rfl c_S0_11_40)) (sr rfl c_S0_11_41)) (sr rfl c_S0_11_42)) (sr rfl c_S0_11_43)) (sr rfl c_S0_11_44)) (sr rfl c_S0_11_45)
lemma c_S0_12_0 : span (chk_S0 12) 8 0 = true := by decide +kernel
lemma c_S0_12_1 : span (chk_S0 12) 8 8 = true := by decide +kernel
lemma c_S0_12_2 : span (chk_S0 12) 8 16 = true := by decide +kernel
lemma c_S0_12_3 : span (chk_S0 12) 8 24 = true := by decide +kernel
lemma c_S0_12_4 : span (chk_S0 12) 8 32 = true := by decide +kernel
lemma c_S0_12_5 : span (chk_S0 12) 8 40 = true := by decide +kernel
lemma c_S0_12_6 : span (chk_S0 12) 8 48 = true := by decide +kernel
lemma c_S0_12_7 : span (chk_S0 12) 8 56 = true := by decide +kernel
lemma c_S0_12_8 : span (chk_S0 12) 8 64 = true := by decide +kernel
lemma c_S0_12_9 : span (chk_S0 12) 8 72 = true := by decide +kernel
lemma c_S0_12_10 : span (chk_S0 12) 8 80 = true := by decide +kernel
lemma c_S0_12_11 : span (chk_S0 12) 8 88 = true := by decide +kernel
lemma c_S0_12_12 : span (chk_S0 12) 8 96 = true := by decide +kernel
lemma c_S0_12_13 : span (chk_S0 12) 8 104 = true := by decide +kernel
lemma c_S0_12_14 : span (chk_S0 12) 8 112 = true := by decide +kernel
lemma c_S0_12_15 : span (chk_S0 12) 8 120 = true := by decide +kernel
lemma c_S0_12_16 : span (chk_S0 12) 8 128 = true := by decide +kernel
lemma c_S0_12_17 : span (chk_S0 12) 8 136 = true := by decide +kernel
lemma c_S0_12_18 : span (chk_S0 12) 8 144 = true := by decide +kernel
lemma c_S0_12_19 : span (chk_S0 12) 8 152 = true := by decide +kernel
lemma c_S0_12_20 : span (chk_S0 12) 8 160 = true := by decide +kernel
lemma c_S0_12_21 : span (chk_S0 12) 8 168 = true := by decide +kernel
lemma c_S0_12_22 : span (chk_S0 12) 2 176 = true := by decide +kernel
lemma all_S0_12 : ∀ i, 0 ≤ i → i < 178 → chk_S0 12 i = true := rj (rj (rj (rj (rj (rj (rj (rj (rj (rj (rj (rj (rj (rj (rj (rj (rj (rj (rj (rj (rj (rj (sr rfl c_S0_12_0) (sr rfl c_S0_12_1)) (sr rfl c_S0_12_2)) (sr rfl c_S0_12_3)) (sr rfl c_S0_12_4)) (sr rfl c_S0_12_5)) (sr rfl c_S0_12_6)) (sr rfl c_S0_12_7)) (sr rfl c_S0_12_8)) (sr rfl c_S0_12_9)) (sr rfl c_S0_12_10)) (sr rfl c_S0_12_11)) (sr rfl c_S0_12_12)) (sr rfl c_S0_12_13)) (sr rfl c_S0_12_14)) (sr rfl c_S0_12_15)) (sr rfl c_S0_12_16)) (sr rfl c_S0_12_17)) (sr rfl c_S0_12_18)) (sr rfl c_S0_12_19)) (sr rfl c_S0_12_20)) (sr rfl c_S0_12_21)) (sr rfl c_S0_12_22)
lemma c_S0_13_0 : span (chk_S0 13) 8 0 = true := by decide +kernel
lemma c_S0_13_1 : span (chk_S0 13) 8 8 = true := by decide +kernel
lemma c_S0_13_2 : span (chk_S0 13) 3 16 = true := by decide +kernel
lemma all_S0_13 : ∀ i, 0 ≤ i → i < 19 → chk_S0 13 i = true := rj (rj (sr rfl c_S0_13_0) (sr rfl c_S0_13_1)) (sr rfl c_S0_13_2)
lemma c_S0_14_0 : span (chk_S0 14) 1 0 = true := by decide +kernel
lemma all_S0_14 : ∀ i, 0 ≤ i → i < 1 → chk_S0 14 i = true := sr rfl c_S0_14_0
lemma hcheck_S0 : ∀ s ≤ 14, ∀ idx < cnt_S0 s,
    stepExpand (2 ^ (12 * 12) - 1) 12 m1_S0 m2_S0 m4_S0 m8_S0 rs_S0 rf_S0 certHit_S0 s (decSt_S0 s idx) = false := by
  have htop : (2 ^ (12 * 12) - 1) = top_S0 := by decide +kernel
  rw [htop]
  have hfail : ∀ k idx, (∀ i, 0 ≤ i → i < cnt_S0 k → chk_S0 k i = true) → idx < cnt_S0 k →
      stepExpand top_S0 12 m1_S0 m2_S0 m4_S0 m8_S0 rs_S0 rf_S0 certHit_S0 k (decSt_S0 k idx) = false := by
    intro k idx hall hi; have h1 := hall idx (Nat.zero_le _) hi; unfold chk_S0 at h1
    cases hse : stepExpand top_S0 12 m1_S0 m2_S0 m4_S0 m8_S0 rs_S0 rf_S0 certHit_S0 k (decSt_S0 k idx) <;> simp only [hse] at h1
    · rfl
    · contradiction
  intro s hs idx hidx; interval_cases s
  · have h0 : cnt_S0 0 = 0 := rfl; omega
  · have h0 : cnt_S0 1 = 0 := rfl; omega
  · have h0 : cnt_S0 2 = 0 := rfl; omega
  · have h0 : cnt_S0 3 = 0 := rfl; omega
  · have h0 : cnt_S0 4 = 0 := rfl; omega
  · have h0 : cnt_S0 5 = 0 := rfl; omega
  · have h0 : cnt_S0 6 = 0 := rfl; omega
  · have h0 : cnt_S0 7 = 0 := rfl; omega
  · have h0 : cnt_S0 8 = 0 := rfl; omega
  · exact hfail 9 idx all_S0_9 hidx
  · exact hfail 10 idx all_S0_10 hidx
  · exact hfail 11 idx all_S0_11 hidx
  · exact hfail 12 idx all_S0_12 hidx
  · exact hfail 13 idx all_S0_13 hidx
  · exact hfail 14 idx all_S0_14 hidx
lemma r_S0_0 : searchCert top_S0 12 m1_S0 m2_S0 m4_S0 m8_S0 rs_S0 rf_S0 certHit_S0 14 (mkLitWt top_S0 litW_S0 [1, 1, 1, 1, 2, 1, 2, 2, 1] false) = false := by decide +kernel
lemma r_S0_1 : searchCert top_S0 12 m1_S0 m2_S0 m4_S0 m8_S0 rs_S0 rf_S0 certHit_S0 14 (mkLitWt top_S0 litW_S0 [1, 1, 1, 1, 2, 1, 2, 2, 1] true) = false := by decide +kernel
lemma no_S0 : ¬ HasMono pos_S0 neg_S0 (initOf vs_S0 true) 14 := by
  have htop : 2 ^ (pos_S0.length * neg_S0.length) - 1 = top_S0 := by decide +kernel
  have hms : checkMasks pos_S0.length neg_S0.length m1_S0 m2_S0 m4_S0 m8_S0 rs_S0 = true := by decide +kernel
  intro h
  obtain ⟨k1, hk1, hm1⟩ := hasMono_to_monoLive (by decide) (by decide) 14 _ h
  obtain ⟨k2, hk2, U, hUW, hUnd, hSU⟩ := monoLive_to_sMonoLive k1 _ hm1
  obtain ⟨hperm, hlen⟩ := classify_U_w9 (by decide) (by decide +kernel) hUW hUnd hSU
  have hk_min : 14 ≤ k2 := by
    by_contra hlt
    have hv : varF 4 ∈ U := by rcases hperm with hp | hp <;> exact hp.mem_iff.2 (by simp [vs_S0])
    have ⟨_, hhm⟩ := one_zero_wire_save_one sub_S0_4.1 k2 U (fun u hu => initOf_mono _ _ u (hUW u hu)) hSU _ hv (by funext x; simp [projV, varF])
    exact sub_S0_4.2 U hUW (hasMono_mono_k (by omega) hhm)
  have hk_le : k2 ≤ 14 := by omega
  have hSub0 : ∀ u ∈ vs_S0.map varF, u ∈ initOf vs_S0 true := fun u hu => by simp [initOf, hu]
  have hk_eq : k2 = 14 := by omega
  subst hk_eq
  rcases hperm with hperm | hperm
  ·
    refine close_ht_case (vs := vs_S0) (tgs := [1, 1, 1, 1, 2, 1, 2, 2, 1]) (withW9 := false) (cap := 14) (by decide) (by decide) (by decide) htop hms (by decide) (by decide) encLit_S0 decSt_S0_ok certHit_S0_sound hcheck_S0 (by omega) ?_ (sMonoLive_perm hperm hSU) r_S0_0
    intro wt hwt; simp only [mkWt, vs_S0, List.zipWith_cons_cons, List.zipWith_nil_left, List.append_nil, List.mem_cons, List.not_mem_nil, or_false, ite_false, Bool.false_eq_true] at hwt; rcases hwt with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact tagOk_of_sub sub_S0_0 hSub0 (Or.inl ⟨rfl, by omega⟩)
    · exact tagOk_of_sub sub_S0_1 hSub0 (Or.inl ⟨rfl, by omega⟩)
    · exact tagOk_of_sub sub_S0_2 hSub0 (Or.inl ⟨rfl, by omega⟩)
    · exact tagOk_of_sub sub_S0_3 hSub0 (Or.inl ⟨rfl, by omega⟩)
    · exact tagOk_of_sub sub_S0_4 hSub0 (Or.inr ⟨rfl, by omega⟩)
    · exact tagOk_of_sub sub_S0_5 hSub0 (Or.inl ⟨rfl, by omega⟩)
    · exact tagOk_of_sub sub_S0_6 hSub0 (Or.inr ⟨rfl, by omega⟩)
    · exact tagOk_of_sub sub_S0_7 hSub0 (Or.inr ⟨rfl, by omega⟩)
    · exact tagOk_of_sub sub_S0_8 hSub0 (Or.inl ⟨rfl, by omega⟩)
  ·
    refine close_ht_case (vs := vs_S0) (tgs := [1, 1, 1, 1, 2, 1, 2, 2, 1]) (withW9 := true) (cap := 14) (by decide) (by decide) (by decide) htop hms (by decide) (by decide) encLit_S0 decSt_S0_ok certHit_S0_sound hcheck_S0 (by omega) ?_ (sMonoLive_perm hperm hSU) r_S0_1
    intro wt hwt; simp only [mkWt, vs_S0, List.zipWith_cons_cons, List.zipWith_nil_left, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false, ite_true] at hwt; rcases hwt with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact tagOk_of_sub sub_S0_0 (fun _ h => h) (Or.inl ⟨rfl, by omega⟩)
    · exact tagOk_of_sub sub_S0_1 (fun _ h => h) (Or.inl ⟨rfl, by omega⟩)
    · exact tagOk_of_sub sub_S0_2 (fun _ h => h) (Or.inl ⟨rfl, by omega⟩)
    · exact tagOk_of_sub sub_S0_3 (fun _ h => h) (Or.inl ⟨rfl, by omega⟩)
    · exact tagOk_of_sub sub_S0_4 (fun _ h => h) (Or.inr ⟨rfl, by omega⟩)
    · exact tagOk_of_sub sub_S0_5 (fun _ h => h) (Or.inl ⟨rfl, by omega⟩)
    · exact tagOk_of_sub sub_S0_6 (fun _ h => h) (Or.inr ⟨rfl, by omega⟩)
    · exact tagOk_of_sub sub_S0_7 (fun _ h => h) (Or.inr ⟨rfl, by omega⟩)
    · exact tagOk_of_sub sub_S0_8 (fun _ h => h) (Or.inl ⟨rfl, by omega⟩)
    · trivial

end PEqualNP.Outside.L_meta_2830

theorem PEqualNP.Outside.L_meta_2830 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 → (∀ x3 ∈ [(3 : ℕ), (6 : ℕ), (12 : ℕ), (17 : ℕ), (24 : ℕ), (33 : ℕ), (66 : ℕ), (132 : ℕ), (160 : ℕ), (264 : ℕ), (288 : ℕ), (320 : ℕ)], x1.eval ((List.ofFn fun (x5 : Fin (9 : ℕ)) => x3.testBit ↑x5) ++ [x3.testBit (0 : ℕ) || x3.testBit (1 : ℕ)]) = Bool.true) → (∀ x4 ∈ [(42 : ℕ), (50 : ℕ), (69 : ℕ), (104 : ℕ), (116 : ℕ), (138 : ℕ), (201 : ℕ), (208 : ℕ), (261 : ℕ), (276 : ℕ), (385 : ℕ), (402 : ℕ)], x1.eval ((List.ofFn fun (x6 : Fin (9 : ℕ)) => x4.testBit ↑x6) ++ [x4.testBit (0 : ℕ) || x4.testBit (1 : ℕ)]) = Bool.false) → (15 : ℕ) ≤ x1.size := by
  intro x1 hM hpos hneg
  by_contra hlt
  have hle : x1.size ≤ 14 := by omega
  have hhm := PEqualNP.Outside.L_meta_2830.circuit_to_hasMono x1 (PEqualNP.Outside.L_meta_2830.initOf PEqualNP.Outside.L_meta_2830.vs_S0 true) PEqualNP.Outside.L_meta_2830.pos_S0 PEqualNP.Outside.L_meta_2830.neg_S0 14 hM hle
    (fun m hm => by rw [PEqualNP.Outside.L_meta_2830.vs_S0, PEqualNP.Outside.L_meta_2830.root_input_map']; exact hpos m hm)
    (fun m hm => by rw [PEqualNP.Outside.L_meta_2830.vs_S0, PEqualNP.Outside.L_meta_2830.root_input_map']; exact hneg m hm)
  exact PEqualNP.Outside.L_meta_2830.no_S0 hhm
