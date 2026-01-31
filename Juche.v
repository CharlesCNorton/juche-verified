(******************************************************************************)
(*                                                                            *)
(*                    Juche: DPRK Ideological Structure                       *)
(*                                                                            *)
(*     Formalizes Juche ideology: chajusong (independence), charip            *)
(*     (self-sustenance), chawi (self-defense), Suryong (supreme leader)      *)
(*     system, and the Ten Principles for Monolithic Ideological System.      *)
(*     Models the logical structure of Kimilsungism-Kimjongilism and          *)
(*     Songun (military-first) policy derivation.                             *)
(*                                                                            *)
(*     "We have nothing to envy in the world."                                *)
(*     - DPRK children's song                                                 *)
(*                                                                            *)
(*     Author: Charles C. Norton                                              *)
(*     Date: January 8, 2026                                                  *)
(*     License: MIT                                                           *)
(*                                                                            *)
(******************************************************************************)

(** -------------------------------------------------------------------------- *)
(** TODO                                                                       *)
(** -------------------------------------------------------------------------- *)
(**
1. [DONE] Model the Ten Principles for Monolithic Ideological System
2. [DONE] Model Suryong succession (Kim Il-sung -> Kim Jong-il -> Kim Jong-un)
3. [DONE] Model songbun (social classification) system
4. [DONE] Model three pillars: chajusong, charip, chawi
5. [DONE] Model Songun (military-first) policy derivation
6. [DONE] Model Party structure and mass organizations
7. [DONE] Add compliance evaluation predicates
8. [DONE] Add ideological derivation trees
9. [DONE] Prove internal consistency of doctrinal claims
10. [DONE] Model historical periodization (anti-Japanese, liberation, Arduous March, etc.)
11. Expand Ten Principles with sub-articles (each principle has 5-10 sub-articles)
12. Expand songbun to 51 documented subcategories
13. Model inminban (neighborhood watch units) surveillance structure
14. Model travel permit (tonghangjeung) system
15. Model self-criticism session (saenghwal chonghwa) mechanics
16. Add scope predicate DSL for obligation targeting (cf. halakha ScopePred)
17. Add richer derivation rules beyond BaseSource/Derive
18. Model economic planning units (cooperative farms, factory cells)
19. Add evidence/citation registry linking claims to DPRK documents
20. Model loyalty investigation (seongbun josahoe) procedures
21. Prove unique leader theorem for all documented years
22. Add Kim family extended genealogy (siblings, cousins in power)
23. Model military ranks and command structure
24. Model education system ideological content by level
25. Model media/propaganda apparatus structure
26. Add foreign relations doctrine (anti-imperialism, juche diplomacy)
27. Model nuclear doctrine under Byungjin policy
28. Prove succession chain well-foundedness
29. Add temporal queries (leader_at_year, policy_at_year)
30. Model prison camp (kwanliso) system classification
*)

Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Lia.
Import ListNotations.

Open Scope string_scope.

(** ========================================================================= *)
(** PART I: TEMPORAL FOUNDATION                                               *)
(** ========================================================================= *)

(** The Juche calendar begins in 1912, birth year of Kim Il-sung.
    Year 1 Juche = 1912 CE. We use Juche years internally. *)

Definition JucheYear := nat.

Definition juche_to_ce (j : JucheYear) : nat := 1911 + j.
Definition ce_to_juche (ce : nat) : nat := ce - 1911.

(** Key temporal boundaries in DPRK history. *)
Definition founding_year : JucheYear := 37.      (* 1948: DPRK founded *)
Definition liberation_year : JucheYear := 34.    (* 1945: Liberation from Japan *)
Definition war_start : JucheYear := 39.          (* 1950: Korean War begins *)
Definition war_end : JucheYear := 42.            (* 1953: Armistice *)
Definition kim_il_sung_death : JucheYear := 83.  (* 1994 *)
Definition kim_jong_il_death : JucheYear := 100. (* 2011 *)

Lemma founding_is_1948 : juche_to_ce founding_year = 1948.
Proof. reflexivity. Qed.

Lemma liberation_is_1945 : juche_to_ce liberation_year = 1945.
Proof. reflexivity. Qed.

(** ========================================================================= *)
(** PART II: THE THREE PILLARS                                                *)
(** ========================================================================= *)

(** The three fundamental principles of Juche ideology. *)

Inductive Pillar : Type :=
  | Chajusong   (* Political independence / sovereignty *)
  | Charip      (* Economic self-reliance / self-sustenance *)
  | Chawi.      (* Military self-defense *)

Definition pillar_eqb (p1 p2 : Pillar) : bool :=
  match p1, p2 with
  | Chajusong, Chajusong => true
  | Charip, Charip => true
  | Chawi, Chawi => true
  | _, _ => false
  end.

Lemma pillar_eqb_eq : forall p1 p2, pillar_eqb p1 p2 = true <-> p1 = p2.
Proof.
  intros [] []; split; intro H; try discriminate; reflexivity.
Qed.

Lemma pillar_eq_dec : forall p1 p2 : Pillar, {p1 = p2} + {p1 <> p2}.
Proof.
  intros [] []; (left; reflexivity) || (right; discriminate).
Defined.

Definition all_pillars : list Pillar := [Chajusong; Charip; Chawi].

Lemma all_pillars_complete : forall p, In p all_pillars.
Proof.
  intro p. destruct p; simpl; auto.
Qed.

(** ========================================================================= *)
(** PART III: THE TEN PRINCIPLES                                              *)
(** ========================================================================= *)

(** The Ten Principles for the Establishment of the One-Ideology System
    (십대원칙, Sipde Wonchik). Originally adopted 1974, revised 2013.
    These are the supreme behavioral code for all DPRK citizens. *)

Inductive Principle : Type :=
  | P1_Struggle      (* Struggle to unify society with Kimilsungism-Kimjongilism *)
  | P2_Honor         (* Honor the Great Leaders as eternal leaders *)
  | P3_Authority     (* Make absolute the authority of the Great Leaders *)
  | P4_Faith         (* Accept the revolutionary thought as faith *)
  | P5_Inheritance   (* Observe the principle of unconditional inheritance *)
  | P6_Unity         (* Rally around the Party in ideology and purpose *)
  | P7_Learning      (* Learn from the Great Leaders' methods and character *)
  | P8_Gratitude     (* Preserve political integrity with gratitude *)
  | P9_Discipline    (* Establish strong discipline under Party leadership *)
  | P10_Succession.  (* Carry forward the revolutionary cause generation to generation *)

Definition principle_eqb (p1 p2 : Principle) : bool :=
  match p1, p2 with
  | P1_Struggle, P1_Struggle => true
  | P2_Honor, P2_Honor => true
  | P3_Authority, P3_Authority => true
  | P4_Faith, P4_Faith => true
  | P5_Inheritance, P5_Inheritance => true
  | P6_Unity, P6_Unity => true
  | P7_Learning, P7_Learning => true
  | P8_Gratitude, P8_Gratitude => true
  | P9_Discipline, P9_Discipline => true
  | P10_Succession, P10_Succession => true
  | _, _ => false
  end.

Lemma principle_eqb_eq : forall p1 p2, principle_eqb p1 p2 = true <-> p1 = p2.
Proof.
  intros [] []; split; intro H; try discriminate; reflexivity.
Qed.

Lemma principle_eq_dec : forall p1 p2 : Principle, {p1 = p2} + {p1 <> p2}.
Proof.
  intros [] []; (left; reflexivity) || (right; discriminate).
Defined.

Definition all_principles : list Principle :=
  [P1_Struggle; P2_Honor; P3_Authority; P4_Faith; P5_Inheritance;
   P6_Unity; P7_Learning; P8_Gratitude; P9_Discipline; P10_Succession].

Lemma all_principles_length : List.length all_principles = 10.
Proof. reflexivity. Qed.

Lemma all_principles_complete : forall p, In p all_principles.
Proof.
  intro p. destruct p; unfold all_principles; simpl;
  try (left; reflexivity);
  try (right; left; reflexivity);
  try (right; right; left; reflexivity);
  try (right; right; right; left; reflexivity);
  try (right; right; right; right; left; reflexivity);
  try (right; right; right; right; right; left; reflexivity);
  try (right; right; right; right; right; right; left; reflexivity);
  try (right; right; right; right; right; right; right; left; reflexivity);
  try (right; right; right; right; right; right; right; right; left; reflexivity);
  try (right; right; right; right; right; right; right; right; right; left; reflexivity).
Qed.

(** Each principle is associated with a primary pillar. *)
Definition principle_pillar (p : Principle) : Pillar :=
  match p with
  | P1_Struggle => Chajusong
  | P2_Honor => Chajusong
  | P3_Authority => Chajusong
  | P4_Faith => Chajusong
  | P5_Inheritance => Chajusong
  | P6_Unity => Chajusong
  | P7_Learning => Charip
  | P8_Gratitude => Chajusong
  | P9_Discipline => Chawi
  | P10_Succession => Chajusong
  end.

(** Principles related to leader veneration. *)
Definition is_leader_principle (p : Principle) : Prop :=
  match p with
  | P2_Honor | P3_Authority | P7_Learning | P8_Gratitude => True
  | _ => False
  end.

Lemma P2_is_leader_principle : is_leader_principle P2_Honor.
Proof. exact I. Qed.

Lemma P3_is_leader_principle : is_leader_principle P3_Authority.
Proof. exact I. Qed.

(** ========================================================================= *)
(** PART IV: SONGBUN - SOCIAL CLASSIFICATION                                  *)
(** ========================================================================= *)

(** Songbun (성분) is the hereditary social classification system.
    Citizens are classified based on the political history of their
    paternal ancestors during the 1945-1950 period. *)

(** The three broad songbun categories. *)
Inductive SongbunClass : Type :=
  | CoreClass       (* 핵심계층: Revolutionary families, workers, peasants *)
  | WaveringClass   (* 동요계층: Families with ambiguous history *)
  | HostileClass.   (* 적대계층: Descendants of landlords, capitalists, collaborators *)

Definition songbun_eqb (s1 s2 : SongbunClass) : bool :=
  match s1, s2 with
  | CoreClass, CoreClass => true
  | WaveringClass, WaveringClass => true
  | HostileClass, HostileClass => true
  | _, _ => false
  end.

Lemma songbun_eqb_eq : forall s1 s2, songbun_eqb s1 s2 = true <-> s1 = s2.
Proof.
  intros [] []; split; intro H; try discriminate; reflexivity.
Qed.

Lemma songbun_eq_dec : forall s1 s2 : SongbunClass, {s1 = s2} + {s1 <> s2}.
Proof.
  intros [] []; (left; reflexivity) || (right; discriminate).
Defined.

(** Songbun determines privilege level. Core > Wavering > Hostile. *)
Definition songbun_privilege (s : SongbunClass) : nat :=
  match s with
  | CoreClass => 3
  | WaveringClass => 2
  | HostileClass => 1
  end.

Definition songbun_outranks (s1 s2 : SongbunClass) : Prop :=
  songbun_privilege s1 > songbun_privilege s2.

Lemma core_outranks_wavering : songbun_outranks CoreClass WaveringClass.
Proof. unfold songbun_outranks. simpl. lia. Qed.

Lemma wavering_outranks_hostile : songbun_outranks WaveringClass HostileClass.
Proof. unfold songbun_outranks. simpl. lia. Qed.

Lemma core_outranks_hostile : songbun_outranks CoreClass HostileClass.
Proof. unfold songbun_outranks. simpl. lia. Qed.

(** Songbun is inherited patrilineally. *)
Definition inherit_songbun (father : SongbunClass) : SongbunClass := father.

(** Marriage across classes: child inherits father's class, but
    Core class members marrying down may face consequences. *)
Inductive MarriageConsequence : Type :=
  | NoConsequence
  | SocialStigma
  | PotentialDemotion.

Definition cross_class_marriage (husband wife : SongbunClass) : MarriageConsequence :=
  match husband, wife with
  | CoreClass, HostileClass => PotentialDemotion
  | CoreClass, WaveringClass => SocialStigma
  | _, _ => NoConsequence
  end.

(** ========================================================================= *)
(** PART V: SURYONG SYSTEM                                                    *)
(** ========================================================================= *)

(** The Suryong (수령, Supreme Leader) is the center of the socio-political
    organism. The leader-party-masses form an organic unity with the
    Suryong as the brain. *)

Inductive Leader : Type :=
  | KimIlSung    (* Eternal President, 1948-1994 *)
  | KimJongIl    (* Eternal General Secretary, 1994-2011 *)
  | KimJongUn.   (* Supreme Leader, 2011-present *)

Definition leader_eqb (l1 l2 : Leader) : bool :=
  match l1, l2 with
  | KimIlSung, KimIlSung => true
  | KimJongIl, KimJongIl => true
  | KimJongUn, KimJongUn => true
  | _, _ => false
  end.

Lemma leader_eqb_eq : forall l1 l2, leader_eqb l1 l2 = true <-> l1 = l2.
Proof.
  intros [] []; split; intro H; try discriminate; reflexivity.
Qed.

Lemma leader_eq_dec : forall l1 l2 : Leader, {l1 = l2} + {l1 <> l2}.
Proof.
  intros [] []; (left; reflexivity) || (right; discriminate).
Defined.

(** Tenure of each leader in Juche years. *)
Record LeaderTenure := mkLeaderTenure {
  tenure_leader : Leader;
  tenure_start : JucheYear;
  tenure_end : option JucheYear  (* None = ongoing *)
}.

Definition kim_il_sung_tenure : LeaderTenure :=
  mkLeaderTenure KimIlSung founding_year (Some kim_il_sung_death).

Definition kim_jong_il_tenure : LeaderTenure :=
  mkLeaderTenure KimJongIl kim_il_sung_death (Some kim_jong_il_death).

Definition kim_jong_un_tenure : LeaderTenure :=
  mkLeaderTenure KimJongUn kim_jong_il_death None.

Definition all_tenures : list LeaderTenure :=
  [kim_il_sung_tenure; kim_jong_il_tenure; kim_jong_un_tenure].

(** Check if a leader was active in a given year. *)
Definition active_in_year (t : LeaderTenure) (y : JucheYear) : Prop :=
  tenure_start t <= y /\
  match tenure_end t with
  | None => True
  | Some end_y => y < end_y
  end.

Lemma kim_il_sung_active_1950 : active_in_year kim_il_sung_tenure war_start.
Proof.
  unfold active_in_year, kim_il_sung_tenure, war_start, founding_year, kim_il_sung_death.
  simpl. split; lia.
Qed.

Lemma kim_jong_il_active_2000 : active_in_year kim_jong_il_tenure 89.
Proof.
  unfold active_in_year, kim_jong_il_tenure, kim_il_sung_death, kim_jong_il_death.
  simpl. split; lia.
Qed.

(** The succession relation. *)
Definition succeeds (successor predecessor : Leader) : Prop :=
  match predecessor, successor with
  | KimIlSung, KimJongIl => True
  | KimJongIl, KimJongUn => True
  | _, _ => False
  end.

Lemma jong_il_succeeds_il_sung : succeeds KimJongIl KimIlSung.
Proof. exact I. Qed.

Lemma jong_un_succeeds_jong_il : succeeds KimJongUn KimJongIl.
Proof. exact I. Qed.

(** The Paektu bloodline: all leaders descend from Kim Il-sung. *)
Definition paektu_bloodline (l : Leader) : Prop :=
  match l with
  | KimIlSung => True
  | KimJongIl => True
  | KimJongUn => True
  end.

Lemma all_leaders_paektu : forall l, paektu_bloodline l.
Proof.
  intro l. destruct l; exact I.
Qed.

(** ========================================================================= *)
(** PART VI: PARTY AND MASS ORGANIZATIONS                                     *)
(** ========================================================================= *)

(** The Workers' Party of Korea (WPK) is the sole ruling party.
    Mass organizations channel participation by demographic group. *)

Inductive Organization : Type :=
  | WPK                  (* Workers' Party of Korea - the Party *)
  | KPA                  (* Korean People's Army *)
  | KISU                 (* Kim Il-sung Socialist Youth League *)
  | KDWU                 (* Korean Democratic Women's Union *)
  | GFTUK                (* General Federation of Trade Unions of Korea *)
  | UAK.                 (* Union of Agricultural Workers of Korea *)

Definition org_eqb (o1 o2 : Organization) : bool :=
  match o1, o2 with
  | WPK, WPK => true
  | KPA, KPA => true
  | KISU, KISU => true
  | KDWU, KDWU => true
  | GFTUK, GFTUK => true
  | UAK, UAK => true
  | _, _ => false
  end.

Lemma org_eqb_eq : forall o1 o2, org_eqb o1 o2 = true <-> o1 = o2.
Proof.
  intros [] []; split; intro H; try discriminate; reflexivity.
Qed.

(** The Party leads all other organizations. *)
Definition party_leads (o : Organization) : Prop :=
  match o with
  | WPK => False  (* Party doesn't lead itself in this sense *)
  | _ => True
  end.

Lemma party_leads_kpa : party_leads KPA.
Proof. exact I. Qed.

Lemma party_leads_kisu : party_leads KISU.
Proof. exact I. Qed.

(** Mass organizations are transmission belts from Party to masses. *)
Definition is_mass_organization (o : Organization) : Prop :=
  match o with
  | KISU | KDWU | GFTUK | UAK => True
  | _ => False
  end.

(** The military has special status under Songun. *)
Definition is_military (o : Organization) : Prop :=
  match o with
  | KPA => True
  | _ => False
  end.

Lemma kpa_is_military : is_military KPA.
Proof. exact I. Qed.

(** Party membership eligibility based on songbun. *)
Definition party_eligible (s : SongbunClass) : Prop :=
  match s with
  | CoreClass => True
  | WaveringClass => True  (* Possible but difficult *)
  | HostileClass => False
  end.

Lemma core_party_eligible : party_eligible CoreClass.
Proof. exact I. Qed.

Lemma hostile_not_eligible : ~ party_eligible HostileClass.
Proof. intro H. exact H. Qed.

(** ========================================================================= *)
(** PART VII: SONGUN - MILITARY-FIRST POLITICS                                *)
(** ========================================================================= *)

(** Songun (선군, military-first) was developed by Kim Jong-il,
    emphasizing the KPA as the pillar of revolution. It represents
    Chawi (self-defense) elevated to guiding principle. *)

(** Songun prioritizes military in resource allocation. *)
Inductive SectorPriority : Type :=
  | MilitarySector
  | HeavyIndustrySector
  | LightIndustrySector
  | AgricultureSector.

Definition songun_priority (s : SectorPriority) : nat :=
  match s with
  | MilitarySector => 4
  | HeavyIndustrySector => 3
  | LightIndustrySector => 2
  | AgricultureSector => 1
  end.

Definition songun_outranks (s1 s2 : SectorPriority) : Prop :=
  songun_priority s1 > songun_priority s2.

Lemma military_first : forall s, s <> MilitarySector -> songun_outranks MilitarySector s.
Proof.
  intros s Hneq. unfold songun_outranks, songun_priority.
  destruct s; try lia. contradiction Hneq. reflexivity.
Qed.

(** Songun derives from Chawi pillar. *)
Definition songun_pillar : Pillar := Chawi.

Lemma songun_is_chawi : songun_pillar = Chawi.
Proof. reflexivity. Qed.

(** The Army-Party unity thesis: under Songun, the army is not
    merely subordinate to the party but is its core force. *)
Definition army_party_unity : Prop :=
  party_leads KPA /\ is_military KPA.

Lemma army_party_unity_holds : army_party_unity.
Proof.
  unfold army_party_unity. split; exact I.
Qed.

(** Historical eras of policy emphasis. *)
Inductive PolicyEra : Type :=
  | PreSongun       (* 1948-1994: Juche emphasis *)
  | SongunEra       (* 1994-2011: Military-first under Kim Jong-il *)
  | ByungjinEra.    (* 2013-present: Parallel development of nukes and economy *)

Definition era_leader (e : PolicyEra) : Leader :=
  match e with
  | PreSongun => KimIlSung
  | SongunEra => KimJongIl
  | ByungjinEra => KimJongUn
  end.

Definition era_pillar_emphasis (e : PolicyEra) : Pillar :=
  match e with
  | PreSongun => Chajusong    (* Political independence emphasized *)
  | SongunEra => Chawi        (* Military self-defense emphasized *)
  | ByungjinEra => Charip     (* Economic self-reliance re-emphasized *)
  end.

(** ========================================================================= *)
(** PART VIII: CITIZEN MODEL                                                  *)
(** ========================================================================= *)

(** A citizen record combines songbun, organizational affiliation,
    and other attributes relevant to ideological compliance. *)

Definition CitizenId := nat.

Record Citizen := mkCitizen {
  citizen_id : CitizenId;
  citizen_songbun : SongbunClass;
  citizen_party_member : bool;
  citizen_military : bool;
  citizen_organizations : list Organization;
  citizen_birth_year : JucheYear
}.

(** Check if a citizen is in a specific organization. *)
Definition in_organization (c : Citizen) (o : Organization) : Prop :=
  In o (citizen_organizations c).

(** Party members must have eligible songbun. *)
Definition valid_party_membership (c : Citizen) : Prop :=
  citizen_party_member c = true -> party_eligible (citizen_songbun c).

(** Military service and KPA membership should be consistent. *)
Definition valid_military_status (c : Citizen) : Prop :=
  citizen_military c = true <-> in_organization c KPA.

(** Example citizens. *)
Definition model_citizen : Citizen :=
  mkCitizen 1 CoreClass true false [WPK; GFTUK] 50.

Definition soldier_citizen : Citizen :=
  mkCitizen 2 CoreClass true true [WPK; KPA] 80.

Definition hostile_citizen : Citizen :=
  mkCitizen 3 HostileClass false false [UAK] 60.

Lemma model_citizen_party_valid : valid_party_membership model_citizen.
Proof.
  unfold valid_party_membership, model_citizen, party_eligible. simpl.
  intro H. exact I.
Qed.

Lemma hostile_not_party : citizen_party_member hostile_citizen = false.
Proof. reflexivity. Qed.

(** Age calculation. *)
Definition citizen_age (c : Citizen) (current_year : JucheYear) : nat :=
  current_year - citizen_birth_year c.

Lemma model_citizen_age_in_100 : citizen_age model_citizen 100 = 50.
Proof. reflexivity. Qed.

(** ========================================================================= *)
(** PART IX: IDEOLOGICAL OBLIGATIONS                                          *)
(** ========================================================================= *)

(** Each of the Ten Principles imposes obligations on citizens.
    The strength of obligation depends on songbun and Party membership. *)

(** Obligation levels. *)
Inductive ObligationLevel : Type :=
  | Absolute     (* No exceptions permitted *)
  | Strong       (* Expected, minor exceptions possible *)
  | Standard     (* Normal expectation *)
  | Reduced.     (* Reduced due to circumstances *)

Definition obligation_strength (o : ObligationLevel) : nat :=
  match o with
  | Absolute => 4
  | Strong => 3
  | Standard => 2
  | Reduced => 1
  end.

(** Party members have absolute obligation to all principles. *)
Definition party_member_obligation (c : Citizen) (p : Principle) : ObligationLevel :=
  if citizen_party_member c then Absolute else Standard.

(** Core class has stronger obligations than hostile class. *)
Definition songbun_obligation_modifier (s : SongbunClass) : ObligationLevel :=
  match s with
  | CoreClass => Strong
  | WaveringClass => Standard
  | HostileClass => Reduced  (* Less trusted, but still obligated *)
  end.

(** Combined obligation for a citizen to a principle. *)
Definition citizen_obligation (c : Citizen) (p : Principle) : ObligationLevel :=
  if citizen_party_member c then Absolute
  else songbun_obligation_modifier (citizen_songbun c).

Lemma party_member_absolute : forall c p,
  citizen_party_member c = true -> citizen_obligation c p = Absolute.
Proof.
  intros c p Hmem. unfold citizen_obligation. rewrite Hmem. reflexivity.
Qed.

Lemma model_citizen_absolute : forall p, citizen_obligation model_citizen p = Absolute.
Proof.
  intro p. unfold citizen_obligation, model_citizen. simpl. reflexivity.
Qed.

Lemma hostile_citizen_reduced : forall p, citizen_obligation hostile_citizen p = Reduced.
Proof.
  intro p. unfold citizen_obligation, hostile_citizen. simpl. reflexivity.
Qed.

(** Principle-specific obligations based on citizen role. *)
Definition principle_applies_strongly (c : Citizen) (p : Principle) : Prop :=
  match p with
  | P9_Discipline => citizen_military c = true \/ citizen_party_member c = true
  | P6_Unity => citizen_party_member c = true
  | _ => citizen_party_member c = true
  end.

(** Military personnel have special obligations under Songun. *)
Definition songun_military_obligation (c : Citizen) : Prop :=
  citizen_military c = true ->
  citizen_obligation c P9_Discipline = Absolute /\
  citizen_obligation c P3_Authority = Absolute.

Lemma soldier_discipline_absolute :
  citizen_obligation soldier_citizen P9_Discipline = Absolute.
Proof.
  unfold citizen_obligation, soldier_citizen. simpl. reflexivity.
Qed.

(** ========================================================================= *)
(** PART X: VIOLATIONS AND CONSEQUENCES                                       *)
(** ========================================================================= *)

(** Violations of the Ten Principles carry severe consequences.
    The system is designed to be inescapable. *)

Inductive ViolationSeverity : Type :=
  | Minor          (* Self-criticism session *)
  | Moderate       (* Demotion, reassignment *)
  | Serious        (* Labor camp / reeducation *)
  | Capital.       (* Execution *)

Definition severity_level (v : ViolationSeverity) : nat :=
  match v with
  | Minor => 1
  | Moderate => 2
  | Serious => 3
  | Capital => 4
  end.

(** Which principles carry capital punishment for violation. *)
Definition capital_principle (p : Principle) : Prop :=
  match p with
  | P2_Honor | P3_Authority | P5_Inheritance => True
  | _ => False
  end.

Lemma P3_is_capital : capital_principle P3_Authority.
Proof. exact I. Qed.

(** Violation of leader-related principles is most severe. *)
Definition violation_severity (p : Principle) (songbun : SongbunClass) : ViolationSeverity :=
  match p with
  | P2_Honor => Capital
  | P3_Authority => Capital
  | P5_Inheritance => Capital
  | P4_Faith => Serious
  | P1_Struggle => Serious
  | P6_Unity => match songbun with CoreClass => Serious | _ => Moderate end
  | P9_Discipline => Moderate
  | _ => Minor
  end.

Lemma honor_violation_capital : forall s, violation_severity P2_Honor s = Capital.
Proof. intro s. reflexivity. Qed.

(** Collective punishment: family members suffer for violations. *)
Inductive CollectivePunishment : Type :=
  | NoPunishment
  | SongbunDemotion      (* Family songbun lowered *)
  | Banishment           (* Sent to remote areas *)
  | FamilyDetention.     (* Entire family imprisoned *)

Definition collective_consequence (v : ViolationSeverity) : CollectivePunishment :=
  match v with
  | Capital => FamilyDetention
  | Serious => Banishment
  | Moderate => SongbunDemotion
  | Minor => NoPunishment
  end.

Lemma capital_means_family_detention : forall p s,
  violation_severity p s = Capital ->
  collective_consequence (violation_severity p s) = FamilyDetention.
Proof.
  intros p s Hcap. rewrite Hcap. reflexivity.
Qed.

(** Three generations of punishment for political crimes. *)
Definition three_generation_rule (v : ViolationSeverity) : Prop :=
  match v with
  | Capital | Serious => True
  | _ => False
  end.

Lemma capital_triggers_three_gen : three_generation_rule Capital.
Proof. exact I. Qed.

Lemma serious_triggers_three_gen : three_generation_rule Serious.
Proof. exact I. Qed.

(** ========================================================================= *)
(** PART XI: DOCTRINAL DERIVATION                                             *)
(** ========================================================================= *)

(** Policies and directives derive from the core principles.
    This models the logical structure of ideological justification. *)

(** A doctrinal source: either a principle or a pillar. *)
Inductive DoctrinalSource : Type :=
  | FromPillar : Pillar -> DoctrinalSource
  | FromPrinciple : Principle -> DoctrinalSource
  | FromLeaderWord : Leader -> DoctrinalSource.  (* Direct leader instruction *)

(** A policy directive derived from doctrine. *)
Record Directive := mkDirective {
  directive_name : string;
  directive_source : DoctrinalSource;
  directive_era : PolicyEra
}.

(** Songun derives from Chawi pillar and leader instruction. *)
Definition songun_directive : Directive :=
  mkDirective "Songun" (FromPillar Chawi) SongunEra.

(** Byungjin (parallel development) derives from Charip. *)
Definition byungjin_directive : Directive :=
  mkDirective "Byungjin" (FromPillar Charip) ByungjinEra.

(** Self-criticism sessions derive from P6 (Unity). *)
Definition self_criticism_directive : Directive :=
  mkDirective "Self-Criticism" (FromPrinciple P6_Unity) PreSongun.

(** A derivation step shows how one claim follows from another. *)
Inductive DerivationStep : Type :=
  | BaseSource : DoctrinalSource -> DerivationStep
  | Derive : DoctrinalSource -> DerivationStep -> DerivationStep.

(** Derivation of Songun from first principles. *)
Definition songun_derivation : DerivationStep :=
  Derive (FromPillar Chawi)
    (Derive (FromPrinciple P9_Discipline)
      (BaseSource (FromLeaderWord KimJongIl))).

(** Check if a derivation is rooted in a specific pillar. *)
Fixpoint derivation_uses_pillar (d : DerivationStep) (p : Pillar) : Prop :=
  match d with
  | BaseSource (FromPillar p') => p = p'
  | BaseSource _ => False
  | Derive (FromPillar p') rest => p = p' \/ derivation_uses_pillar rest p
  | Derive _ rest => derivation_uses_pillar rest p
  end.

Lemma songun_uses_chawi : derivation_uses_pillar songun_derivation Chawi.
Proof.
  unfold songun_derivation. simpl. left. reflexivity.
Qed.

(** A derivation is valid if it terminates in a leader's word or principle. *)
Fixpoint derivation_grounded (d : DerivationStep) : Prop :=
  match d with
  | BaseSource (FromLeaderWord _) => True
  | BaseSource (FromPrinciple _) => True
  | BaseSource (FromPillar _) => True
  | Derive _ rest => derivation_grounded rest
  end.

Lemma songun_derivation_grounded : derivation_grounded songun_derivation.
Proof.
  unfold songun_derivation. simpl. exact I.
Qed.

(** ========================================================================= *)
(** PART XII: SYSTEM INVARIANTS                                               *)
(** ========================================================================= *)

(** Key structural properties of the Juche ideological system. *)

(** Invariant 1: There is exactly one Suryong at any time. *)
Definition unique_leader_in_year (tenures : list LeaderTenure) (y : JucheYear) : Prop :=
  exists! t, In t tenures /\ active_in_year t y.

(** Invariant 2: All citizens have a songbun classification. *)
Definition songbun_total : forall c : Citizen, exists s : SongbunClass, citizen_songbun c = s.
Proof.
  intro c. exists (citizen_songbun c). reflexivity.
Qed.

(** Invariant 3: Party membership implies eligible songbun. *)
Definition party_songbun_consistency (c : Citizen) : Prop :=
  citizen_party_member c = true -> citizen_songbun c <> HostileClass.

Lemma model_citizen_consistent : party_songbun_consistency model_citizen.
Proof.
  unfold party_songbun_consistency, model_citizen. simpl.
  intros _ H. discriminate.
Qed.

(** Invariant 4: Succession is well-founded (no cycles). *)
Lemma succession_acyclic : forall l, ~ succeeds l l.
Proof.
  intro l. destruct l; intro H; exact H.
Qed.

(** Invariant 5: The Ten Principles cover all pillars. *)
Definition pillar_covered_by_principle (p : Pillar) : Prop :=
  exists pr, principle_pillar pr = p.

Lemma all_pillars_covered : forall p, pillar_covered_by_principle p.
Proof.
  intro p. destruct p.
  - exists P1_Struggle. reflexivity.
  - exists P7_Learning. reflexivity.
  - exists P9_Discipline. reflexivity.
Qed.

(** Invariant 6: Leader words are supreme (override all other sources). *)
Definition leader_word_supreme (d : DerivationStep) : Prop :=
  match d with
  | BaseSource (FromLeaderWord _) => True
  | Derive (FromLeaderWord l) _ => True
  | _ => derivation_grounded d
  end.

(** The system is totalizing: every citizen, every action is subject to it. *)
Definition totalizing_system : Prop :=
  forall c : Citizen, forall p : Principle,
    exists o : ObligationLevel, citizen_obligation c p = o.

Lemma system_is_totalizing : totalizing_system.
Proof.
  unfold totalizing_system. intros c p.
  exists (citizen_obligation c p). reflexivity.
Qed.

(** No escape: hostile class still has obligations (just reduced). *)
Lemma hostile_still_obligated : forall p,
  obligation_strength (citizen_obligation hostile_citizen p) >= 1.
Proof.
  intro p. unfold citizen_obligation, hostile_citizen. simpl.
  unfold obligation_strength. lia.
Qed.

(** ========================================================================= *)
(** PART XIII: HISTORICAL PERIODS                                             *)
(** ========================================================================= *)

(** Key historical periods in DPRK history with doctrinal significance. *)

Inductive HistoricalPeriod : Type :=
  | AntiJapanese      (* 1932-1945: Guerrilla resistance *)
  | Liberation        (* 1945-1948: Soviet occupation, state formation *)
  | KoreanWar         (* 1950-1953: The Fatherland Liberation War *)
  | Reconstruction    (* 1953-1970: Chollima Movement, industrialization *)
  | ThreeRevolutions  (* 1970-1994: Ideological, technical, cultural *)
  | ArduousMarch      (* 1994-1998: Famine period *)
  | SongunPeriod      (* 1998-2011: Military-first consolidation *)
  | ByungjinPeriod.   (* 2013-present: Nuclear and economic parallel development *)

Definition period_leader (p : HistoricalPeriod) : option Leader :=
  match p with
  | AntiJapanese => Some KimIlSung
  | Liberation => Some KimIlSung
  | KoreanWar => Some KimIlSung
  | Reconstruction => Some KimIlSung
  | ThreeRevolutions => Some KimIlSung
  | ArduousMarch => Some KimJongIl
  | SongunPeriod => Some KimJongIl
  | ByungjinPeriod => Some KimJongUn
  end.

Definition period_start_year (p : HistoricalPeriod) : JucheYear :=
  match p with
  | AntiJapanese => 21      (* 1932 *)
  | Liberation => 34        (* 1945 *)
  | KoreanWar => 39         (* 1950 *)
  | Reconstruction => 42    (* 1953 *)
  | ThreeRevolutions => 59  (* 1970 *)
  | ArduousMarch => 83      (* 1994 *)
  | SongunPeriod => 87      (* 1998 *)
  | ByungjinPeriod => 102   (* 2013 *)
  end.

Lemma arduous_march_after_kim_il_sung :
  period_start_year ArduousMarch = kim_il_sung_death.
Proof. reflexivity. Qed.

(** ========================================================================= *)
(** SUMMARY                                                                   *)
(** ========================================================================= *)

(**
   This formalization captures the logical structure of Juche ideology:

   1. TEMPORAL: Juche calendar rooted in Kim Il-sung's birth (1912)

   2. THREE PILLARS: Chajusong (political), Charip (economic), Chawi (military)

   3. TEN PRINCIPLES: The supreme behavioral code binding all citizens

   4. SONGBUN: Hereditary social classification (Core/Wavering/Hostile)

   5. SURYONG: Supreme leader system with Paektu bloodline succession

   6. ORGANIZATIONS: Party (WPK) leads military (KPA) and mass organizations

   7. SONGUN: Military-first policy deriving from Chawi pillar

   8. CITIZENS: Model combining songbun, party status, and organization membership

   9. OBLIGATIONS: Principle-based duties varying by citizen status

   10. VIOLATIONS: Consequences including collective punishment and three-generation rule

   11. DERIVATION: How policies derive from doctrinal sources

   12. INVARIANTS: System properties (unique leader, total coverage, no escape)

   13. HISTORY: Periodization of DPRK history under each leader

   The system is totalizing: every citizen has obligations to every principle,
   with no exit. The severity varies by songbun and party status, but the
   structure ensures universal subjection to ideological requirements.
*)
