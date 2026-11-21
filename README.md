# Kaprekar — audit comparatif indépendant

Dépôt privé de vérification de l'Exploration 005 (Lean 4.19.0, Std) et du dépôt public galyavin/kaprekar-dynamics.

## Préparation
Déposer les fichiers sources **K.lean** et **Replay.lean** de l'archive originale dans `exploration005/`, sans les modifier. Le fichier binaire K.olean n'est pas nécessaire : il est reconstruit par le workflow.

## Exécution
Dans Actions, choisir **Audit comparatif Kaprekar 005 vs galyavin**, puis **Run workflow**. Deux jobs indépendants produisent des artefacts de journaux.

## Statut
La présence du workflow n'atteste ni compilation ni certification. Les résultats doivent être lus dans les journaux d'une exécution réussie. Les recherches bibliographiques et les priorités ne sont pas certifiées par GitHub Actions.
