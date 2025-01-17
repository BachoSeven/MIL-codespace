# Lean Codespace

Questa repo contiene un semplice progetto in Lean con Mathlib che può essere lanciato con un click su GitHub CodeSpace (ambiente di sviluppo nel cloud dal browser) provarlo senza dover installare nulla in locale.

## GitHub / GitHub Pro con Unipi

GitHub già offre 120h gratuite al mese di utilizzo di CodeSpaces, inoltre [Unipi con GitHub Pro](https://www.dm.unipi.it/github-pro/) ci fa arrivare a 180h gratuite di utilizzo al mese.

[![Open in GitHub Codespaces](https://github.com/codespaces/badge.svg)](https://github.com/codespaces/new?skip_quickstart=true&hide_repo_select=true&ref=main&repo=706127139&machine=standardLinux32gb&location=WestEurope)

> :warning: **Achtung** :warning:
>
> - Le 120h o 180h sono "core hours" quindi con la macchina da 2 core sono complessivamente 60h o 90h effettive al mese (per far compilare tutto più velocemente all'inizio conviene usare quella da 4 core ma poi si può passare a quella da 2). Essenzialmente conviene usare con parsimonia le ore di questi GitHub CodeSpaces.
>
> - In particolare quando si ha finito di utilizzare il codespace ricordarsi di spegnerlo dalla pagina <https://github.com/codespaces>, dalla lista di codespaces se c'è scritto ancora **"Active"** premere sui tre puntini e fare **"Stop Container"**.

Per provare che tutto funzioni andare in `./Prova/MathlibExample.lean` e verificare che si apra il pannello laterale e che mettendo il mouse sopra `#check TopologicalSpace` venga mostrata la stringa `TopologicalSpace.{u} (α : Type u) : Type u` (all'inizio vengono compilate molte cose quindi potrebbe comparire per qualche minuto un underline blue sotto il primo import)

## Siti Utili

- https://lean-lang.org/theorem_proving_in_lean4/

- https://lean-lang.org/lean4/doc/

- <https://github.com/leanprover/lean4-samples> (da cui è stato ricavato il codice per questa repo)
