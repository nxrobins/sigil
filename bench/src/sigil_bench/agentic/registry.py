"""Multi-provider model registry + key loading + backend construction.

Provider data (model ids, base URLs, env-var names) is self-contained here;
the backends support *tool use* (function calling), which the agentic harness
requires.

Two backend shapes cover every provider:
  * `anthropic`               → native Anthropic tools  (AnthropicToolBackend)
  * everything OpenAI-compatible → OpenAI `tools` schema (OpenAIToolBackend)
    (openai, openrouter, nebius, xai, azure, mistral, moonshot)

Keys are loaded from a `.env` file (default: the repo-root `.env`)
without overriding anything already in the process environment.
"""

from __future__ import annotations

import os
from dataclasses import dataclass
from pathlib import Path

from dotenv import load_dotenv

# ── Provider table ─────────────────────────────────────────────────────────


@dataclass(frozen=True)
class ProviderInfo:
    name: str
    kind: str  # "anthropic" | "openai"  (the backend shape)
    key_env: str
    base_url: str | None = None  # None → SDK default (real OpenAI / Anthropic)
    # Azure needs endpoint + api-version env vars instead of a base_url.
    azure: bool = False


PROVIDERS: dict[str, ProviderInfo] = {
    "anthropic": ProviderInfo("anthropic", "anthropic", "ANTHROPIC_API_KEY"),
    "openai": ProviderInfo("openai", "openai", "OPENAI_API_KEY"),
    "openrouter": ProviderInfo(
        "openrouter", "openai", "OPENROUTER_API_KEY",
        base_url="https://openrouter.ai/api/v1",
    ),
    "nebius": ProviderInfo(
        "nebius", "openai", "NEBIUS_API_KEY",
        base_url="https://api.tokenfactory.nebius.com/v1/",
    ),
    "xai": ProviderInfo(
        "xai", "openai", "XAI_API_KEY", base_url="https://api.x.ai/v1",
    ),
    "mistral": ProviderInfo(
        "mistral", "openai", "MISTRAL_API_KEY",
        base_url="https://api.mistral.ai/v1",
    ),
    "moonshot": ProviderInfo(
        "moonshot", "openai", "MOONSHOT_API_KEY",
        base_url="https://api.moonshot.ai/v1",
    ),
    "azure": ProviderInfo(
        "azure", "openai", "COVENANT_AZURE_KEY", azure=True,
    ),
}


@dataclass(frozen=True)
class ModelSpec:
    key: str  # short friendly handle used on the CLI
    provider: str  # key into PROVIDERS
    api_model_id: str  # the id sent on the wire
    display_name: str

    @property
    def provider_info(self) -> ProviderInfo:
        return PROVIDERS[self.provider]


# Curated, known-good tool-callers. IDs match the live APIs as of 2026-06.
REGISTRY: dict[str, ModelSpec] = {
    # ── Anthropic (native tools) ──
    "claude-fable-5": ModelSpec("claude-fable-5", "anthropic", "claude-fable-5", "Claude Fable 5"),
    "claude-opus": ModelSpec("claude-opus", "anthropic", "claude-opus-4-8", "Claude Opus 4.8"),
    "claude-sonnet": ModelSpec("claude-sonnet", "anthropic", "claude-sonnet-4-6", "Claude Sonnet 4.6"),
    "claude-haiku": ModelSpec("claude-haiku", "anthropic", "claude-haiku-4-5-20251001", "Claude Haiku 4.5"),
    # ── OpenAI ──
    "gpt-4o": ModelSpec("gpt-4o", "openai", "gpt-4o", "GPT-4o"),
    "gpt-4o-mini": ModelSpec("gpt-4o-mini", "openai", "gpt-4o-mini", "GPT-4o mini"),
    "gpt-5.4": ModelSpec("gpt-5.4", "openai", "gpt-5.4", "GPT-5.4"),
    # ── OpenRouter (cross-provider gateway) ──
    "or-sonnet": ModelSpec("or-sonnet", "openrouter", "anthropic/claude-sonnet-4.6", "Claude Sonnet 4.6 (OpenRouter)"),
    "or-gpt-4o": ModelSpec("or-gpt-4o", "openrouter", "openai/gpt-4o", "GPT-4o (OpenRouter)"),
    "or-llama-70b": ModelSpec("or-llama-70b", "openrouter", "meta-llama/llama-3.3-70b-instruct", "Llama 3.3 70B (OpenRouter)"),
    # ── Nebius ──
    "llama-70b": ModelSpec("llama-70b", "nebius", "meta-llama/Llama-3.3-70B-Instruct", "Llama 3.3 70B (Nebius)"),
    "deepseek": ModelSpec("deepseek", "nebius", "deepseek-ai/DeepSeek-V3.2", "DeepSeek V3.2 (Nebius)"),
    # ── xAI ──
    "grok": ModelSpec("grok", "xai", "grok-4.20-reasoning", "Grok 4.20 Reasoning"),
    # ── Azure AI Foundry (Covenant Labs) ──
    "gpt-5.5-azure": ModelSpec("gpt-5.5-azure", "azure", "gpt-5.5", "GPT-5.5 (Azure AI Foundry)"),
    # ── Mistral ──
    "mistral-large": ModelSpec("mistral-large", "mistral", "mistral-large-latest", "Mistral Large"),
}

# A small, reliably-tool-calling default. Spans two providers (Anthropic +
# OpenAI); both support function calling robustly.
DEFAULT_ROSTER: tuple[str, ...] = (
    "claude-sonnet",
    "claude-haiku",
    "gpt-4o",
    "gpt-4o-mini",
)

# Generic passthrough prefixes: `--models or:deepseek/deepseek-chat` etc. Lets
# an operator name any model on any provider without editing the registry.
_PASSTHROUGH_PREFIXES = {
    "or": "openrouter",
    "openrouter": "openrouter",
    "openai": "openai",
    "nebius": "nebius",
    "xai": "xai",
    "mistral": "mistral",
    "moonshot": "moonshot",
    "anthropic": "anthropic",
}


def resolve_model(name: str) -> ModelSpec:
    """Resolve a CLI model name to a ModelSpec.

    Accepts a registry key (`claude-sonnet`) or a `provider:model_id`
    passthrough (`or:deepseek/deepseek-chat`, `nebius:Qwen/Qwen2.5-72B`).
    """
    if name in REGISTRY:
        return REGISTRY[name]
    if ":" in name:
        prefix, model_id = name.split(":", 1)
        provider = _PASSTHROUGH_PREFIXES.get(prefix)
        if provider and model_id:
            return ModelSpec(name, provider, model_id, f"{model_id} ({provider})")
    raise KeyError(
        f"unknown model {name!r}. Known keys: {sorted(REGISTRY)}; "
        f"or use a passthrough like 'or:<model_id>'."
    )


# ── Env / availability ──────────────────────────────────────────────────────


def default_env_file() -> Path:
    """The repo-root `.env` (where the multi-provider keys live)."""
    # repo_root/.env — resolved upward from this file's location.
    here = Path(__file__).resolve()
    for ancestor in here.parents:
        candidate = ancestor / ".env"
        if candidate.is_file():
            return candidate
    # No file found anywhere above; name the conventional location anyway so
    # the caller's error message says where to put one.
    return Path(".env")


def load_keys(env_file: Path | None = None) -> Path | None:
    """Load API keys from `env_file` (default: the repo-root .env) WITHOUT
    overriding anything already set in the environment. Returns the path that
    was loaded, or None if no file was found (process env is used as-is)."""
    path = env_file or default_env_file()
    if path and Path(path).is_file():
        load_dotenv(path, override=False)
        return Path(path)
    # Also pick up a local .env if present (harmless).
    load_dotenv(override=False)
    return None


def provider_available(provider: str) -> bool:
    info = PROVIDERS[provider]
    if not os.environ.get(info.key_env):
        return False
    if info.azure:
        return bool(os.environ.get("COVENANT_AZURE_ENDPOINT"))
    return True


def is_available(spec: ModelSpec) -> bool:
    return provider_available(spec.provider)


# ── Backend construction ─────────────────────────────────────────────────────


def build_backend(
    spec: ModelSpec, *, request_timeout: float = 120.0,
    thinking: bool = False, effort: str = "high", temperature: float | None = None,
    seed: int | None = None,
):
    """Construct a tool-use backend for `spec`. Imports the SDK lazily so the
    harness only needs the SDKs for providers it actually uses. `thinking`
    (Anthropic only) enables ADAPTIVE thinking at the given `effort` — parity
    with reasoning models like gpt-5.x that think before answering."""
    from .backends import AnthropicToolBackend, OpenAIToolBackend

    info = spec.provider_info
    api_key = os.environ.get(info.key_env)
    if not api_key:
        raise RuntimeError(
            f"model {spec.key!r} needs {info.key_env} but it is not set "
            f"(provider {spec.provider})."
        )

    if info.kind == "anthropic":
        import anthropic

        client = anthropic.Anthropic(api_key=api_key, timeout=request_timeout)
        return AnthropicToolBackend(
            client, spec.api_model_id, thinking=thinking, effort=effort, temperature=temperature
        )

    # OpenAI-compatible (openai, openrouter, nebius, xai, azure, mistral, moonshot)
    if info.azure:
        from openai import AzureOpenAI

        client = AzureOpenAI(
            api_key=api_key,
            azure_endpoint=os.environ["COVENANT_AZURE_ENDPOINT"],
            api_version=os.environ.get("COVENANT_AZURE_API_VERSION", "2025-04-01-preview"),
            timeout=request_timeout,
        )
    else:
        from openai import OpenAI

        kwargs: dict = {"api_key": api_key, "timeout": request_timeout}
        if info.base_url:
            kwargs["base_url"] = info.base_url
        client = OpenAI(**kwargs)
    return OpenAIToolBackend(client, spec.api_model_id, temperature=temperature, seed=seed)
