import sys
import time

from openai import OpenAI

from generator.Key import Key


class LLM:
    def __init__(self, key: Key, system_message: str = "", user_message: str = "", max_tokens: int = 1024,
                 model: str = "gpt-3.5-turbo", messages: list = None,
                 temperature: float = 0.7, n: int = 5, frequency_penalty: float = 0, presence_penalty: float = 0, api_base: str = "", logger: object = None) -> object:
        self.key = key
        self.system_message = system_message
        self.user_message = user_message
        self.max_tokens = max_tokens
        self.model = model
        self.messages = self._default_messages(messages)
        self.temperature = temperature
        self.n = n
        self.frequency_penalty = frequency_penalty
        self.presence_penalty = presence_penalty
        self.api_base = api_base
        self.logger = logger

    @staticmethod
    def _default_messages(messages):
        if messages is None:
            return [{"role": "system", "content": "You are a helpful assistant."},
                    {"role": "user", "content": "Hi!"}]
        else:
            return messages

    def init_model_messages(self):
        self.messages = []

    def add_system_message(self, system_message):
        self.messages.append({"role": "system", "content": system_message})

    def add_examples(self, examples):
        """for count, example in enumerate(examples):
            examples_str = f"\n#Examples{count + 1}\n\n" + example
            self.messages.append({"role": "user", "content": examples_str})"""
        self.messages.extend(examples)

    def add_problem(self, problem):
        self.messages.extend(problem)

    def responses(self, failure_limit=5, failure_sleep=20):
        api_key = self.key.get_key(self.key.key_index)
        if api_key == -1:
            print("not key")
            sys.exit(0)

        if not "" == self.api_base:
            client = OpenAI(
                base_url=self.api_base,
                api_key=api_key
            )
        else:
            client = OpenAI(
                api_key=api_key
            )
        self.logger.info(self.messages)

        while True:
            try:
                self.logger.info(api_key)
                self.logger.info(self.key.key_index)
                response = []
                response = client.chat.completions.create(
                    model=self.model,
                    messages=self.messages,
                    temperature = self.temperature,
                    max_tokens = self.max_tokens,
                    frequency_penalty = self.frequency_penalty,
                    n = self.n,
                    presence_penalty = self.presence_penalty
                )
                break
            except Exception as e:
                self.logger.warning(str(e))
                if failure_limit > 0:
                    if 'Error communicating with OpenAI' in str(e) or 'Connection error' in str(e):
                        self.logger.warning(str(e))
                        sys.exit(0)
                    elif 'Please add a payment method to your account to increase your rate limit' in str(e) or "You " \
                                                                                                              "exceeded your current quota,please check your plan and billing details." in str(e) or '无效的令牌' in str(e) or 'Rate limit' in str(e) or 'requests per day (RPD): Limit' in str(e) or '令牌额度不足' in str(e):
                        self.logger.warning(str(e))
                        self.key.key_index = self.key.key_index + 1
                        api_key = self.key.get_key(self.key.key_index)
                        if api_key == -1:
                            self.logger.warning("所有openAI keys 被限速,或没有key")
                            self.logger.warning("当前key index " + str(self.key.key_index))
                            self.logger.warning(str(e))
                            sys.exit(0)
                        if not "" == self.api_base:
                            client = OpenAI(
                                base_url=self.api_base,
                                api_key=api_key
                            )
                        else:
                            client = OpenAI(
                                api_key=api_key
                            )
                        failure_limit -= 1
                        time.sleep(failure_sleep)
                        continue
                    elif "Connection error" in str(e):
                        self.logger.warning(str(e))
                        sys.exit(0)
                    elif "This model's maximum context length" in str(e):
                        self.logger.warning(str(e))
                        return [],str(e)
                    failure_limit -= 1
                else:
                    self.logger.warning("too many failures, giving up")
                    return [],"too many failures, giving up"
        if response is None or response == []:
            return [], ""
        else:
            self.logger.info(response)
            return [choice.message.content for choice in response.choices if choice.message.content != None], ""


