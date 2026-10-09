# Монитор безопасности: Isabelle/HOL → Rust

Проект формализует политику конфиденциальности в Isabelle/HOL и экспортирует исполнимую часть в Rust. Теория задаёт абстрактные запросы (`i_action`), доменные действия с мандатом (`s_action`) и гомоморфизм `h` между ними. Кодогенератор печатает эти определения как модуль `security_monitor`.

## Состав

| Файл | Назначение |
| --- | --- |
| `Security_Patterns.thy` | Модель: типы, субъект, предикат `conf_i_action`, гомоморфизм `h`, леммы |
| `Codegen_Rust.thy` | Таргет `Rust` для кодогенератора Isabelle 2025 |
| `Export_Rust.thy` | Экспорт `conf_i_action`, `h`, `req_const`, `checkRight_const` |
| `ROOT` | Сессия `Rust_Export` |
| `src/security_monitor.rs` | Сгенерированный модуль. Его перезаписывает `export_code` |
| `src/lib.rs` | Обёртка библиотеки и тесты политики |
| `src/main.rs` | Демонстрация тех же сценариев в консоли |

## Требования

- Isabelle 2025 (`isabelle` в `PATH`)
- Rust и Cargo (`rustc`, `cargo`)

Команды ниже запускаются из каталога проекта:

```bash
cd /home/redbeard/codegen-rust
```

## Перегенерация Rust из теории

Сессия проверяет теории и заново записывает `src/security_monitor.rs`.

```bash
isabelle build -d . Rust_Export
```

Экспортируются константы `conf_i_action`, `h`, `req_const` и `checkRight_const` в модуль `security_monitor`.

## Тесты политики

```bash
cargo test --offline
```

Три теста повторяют утверждения теории:

- `legitimate_request_is_confidential` — лемма `confReq`: запрос субъекта `S` к данным `PR` разрешён;
- `external_agent_is_rejected` — теорема `confReq_AttackFailed`, закрытая через `oops`: запрос `ExternalAgent` к `PR` отклонён;
- `homomorphism_preserves_policy` — теорема `confReqH`: `h(checkRight_const)` удовлетворяет той же политике.

## Запуск монитора

```bash
cargo run --offline
```

Ожидаемый вывод:

```
security monitor
  subject request i_action_ext(S, at, PR, ()) -> allow
  external agent  i_action_ext(ExternalAgent, at, PR, ()) -> deny
  h(checkRight)   i_action_ext(S, at, PR, ()) -> allow
  h(checkRight) = req_const -> yes
```

Программа завершается с кодом 0, если все четыре строки совпадают с политикой. Иначе она печатает `policy check failed` и завершается с кодом 1.

Субъект в `main.rs` — агент `S`, у которого среди абстрактных действий есть `req_const` (`S`, доступ `at`, данные `PR`), а множество доменных действий пусто.

## Граница генератора

Таргет `Rust` печатает исполнимый фрагмент этой модели: алгебраические типы, записи, уравнения, `bool`, `unit`, списки, множества и класс `HOL.equal`. Произвольная теория Isabelle в этот формат не переводится.
